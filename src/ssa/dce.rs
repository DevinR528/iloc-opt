use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
	iloc::{Function, Instruction, Loc, Reg, Val},
	ssa::{postorder, reverse_postorder, DominatorTree},
	OrdLabel,
};

impl Instruction {
	fn is_critical(&self) -> bool {
		matches!(
			self,
			Instruction::ImmRet(..)
				| Instruction::Ret
				| Instruction::PutChar(..)
				| Instruction::IRead(..)
				| Instruction::FRead(..)
				| Instruction::IWrite(..)
				| Instruction::SWrite(..)
				| Instruction::FWrite(..)
				| Instruction::Store { .. }
				| Instruction::StoreAdd { .. }
				| Instruction::StoreAddImm { .. }
				| Instruction::Jump(..)
				| Instruction::ImmJump(..)
				| Instruction::Call { .. }
				| Instruction::ImmCall { .. }
				| Instruction::Malloc { .. }
				| Instruction::Realloc { .. }
				| Instruction::Free(..)
				| Instruction::Frame { .. }
				| Instruction::ImmLoad { src: Val::Location(..), .. }
		)
	}
}

pub fn dead_code(func: &mut Function, domtree: &DominatorTree, start: &OrdLabel) {
	let mut stack = VecDeque::new();
	let mut critical_map = HashSet::new();
	let mut def_map = HashMap::new();

	let mut copied_blocks = vec![];
	for blk in &func.blocks {
		copied_blocks.push((OrdLabel::new(&blk.label), blk.instructions().collect::<Vec<_>>()));
	}
	for (b_label, blk) in &copied_blocks {
		for &inst in blk {
			// If it's critical and we haven't seen it before
			if inst.is_critical() && critical_map.insert(inst) {
				stack.push_back((inst, b_label));
			}

			if let Some(reg) = inst.target_reg() {
				def_map.insert(*reg, (inst, b_label));
			} else {
				match inst {
					Instruction::ImmRCall { ret: reg, .. }
					| Instruction::ImmCall { ret: reg, .. } => {
						def_map.insert(*reg, (inst, b_label));
					}
					Instruction::Frame { params: args, .. } => {
						for reg in args {
							def_map.insert(*reg, (inst, b_label));
						}
					}
					Instruction::Phi(reg, _set, Some(subs)) => {
						let mut reg = *reg;
						reg.as_phi(*subs);
						def_map.insert(reg, (inst, b_label));
					}
					_ => {}
				}
			}
		}
	}

	let empty = BTreeSet::new();
	while let Some((inst, b_label)) = stack.pop_front() {
		let (a, b) = inst.operands();
		if let Some((a_inst, a_blk)) = a.and_then(|a| a.opt_reg()).and_then(|a| def_map.get(&a)) {
			if critical_map.insert(a_inst) {
				stack.push_back((a_inst, a_blk));
			}
		}
		if let Some((b_inst, b_blk)) = b.and_then(|b| b.opt_reg()).and_then(|b| def_map.get(&b)) {
			if critical_map.insert(b_inst) {
				stack.push_back((b_inst, b_blk));
			}
		}

		match inst {
			Instruction::Call { args, .. }
			| Instruction::ImmCall { args, .. }
			| Instruction::Frame { params: args, .. } => {
				for (inst, blk) in args.iter().filter_map(|r| def_map.get(r)) {
					if critical_map.insert(inst) {
						stack.push_back((inst, blk));
					}
				}
			}
			Instruction::Phi(r, set, _) => {
				for (inst, blk) in set.iter().filter_map(|subs| {
					let mut phi = *r;
					phi.as_phi(*subs);
					def_map.get(&phi)
				}) {
					if critical_map.insert(inst) {
						stack.push_back((inst, blk));
					}
				}
			}
			Instruction::Store { dst, .. }
			| Instruction::StoreAddImm { dst, .. }
			| Instruction::StoreAdd { dst, .. } => {
				if let Some((inst, blk)) = def_map.get(dst) {
					if critical_map.insert(inst) {
						stack.push_back((inst, blk));
					}
				}
			}
			_ => (),
		}

		// Control dependence
		// Which blocks does `b_label` control the execution of (where does this block
		// jump/branch/fall-through to)
		for blk in domtree.post_dom_frontier.get(b_label).unwrap_or(&empty) {
			let Some(block) = func.blocks.iter()
				.find(|b| {
					b.label == blk.as_str()
				}) else {
					println!("oh shit {}", blk.as_str());
					continue;
				};

			// TODO: A fall through would be important also...
			let Some(last_inst) = block.instructions.iter()
				.find(|i|
					i.is_cnd_jump() || matches!(i, Instruction::ImmJump(..))
				) else {
					continue;
				};

			if critical_map.insert(last_inst) {
				stack.push_back((last_inst, blk));
			}
		}
	}

	let mut jumps = vec![];
	let mut remove = vec![];
	for (b, blk) in func.blocks.iter().enumerate() {
		for (i, inst) in
			blk.instructions.iter().enumerate().filter(|(_, i)| !matches!(i, Instruction::Skip(..)))
		{
			if !critical_map.contains(&inst) {
				if inst.is_cnd_jump() {
					// post dominance
					// Which blocks will for sure run next (so we can jump to it)
					if let Some(label) = domtree.post_idom_map.get(blk.label.as_str()) {
						// println!("rewrite branch to jump {} -> {:?}", inst, label);
						jumps.push((b, i, Instruction::ImmJump(Loc(label.to_string()))));
					}
				} else if !matches!(inst, Instruction::ImmJump(..) | Instruction::Label(..)) {
					remove.push((b, i));
				}
			}
		}
	}

	for (b, i) in remove {
		func.blocks[b].instructions[i] =
			Instruction::Skip(format!("[ssadce] {}", func.blocks[b].instructions[i]));
	}
	for (b, i, inst) in jumps {
		func.blocks[b].instructions[i] = inst;
	}

	cleanup(func, start);
}

pub fn cleanup(func: &mut Function, start: &OrdLabel) {
	let exit = OrdLabel::exit();

	let mut cfg_map = build_stripped_cfg(func);

	let mut to_jump = vec![];
	let mut changed = true;
	while changed {
		let mut cfg_preds: HashMap<_, BTreeSet<_>> = HashMap::new();
		for (from, tos) in &cfg_map {
			for to in tos {
				cfg_preds.entry(to.clone()).or_default().insert(from.clone());
			}
		}

		changed = false;
		for blk in postorder(&cfg_map, start) {
			// TODO: this should be ok... it was needed at one point
			// if blk.as_str().starts_with(".pre.") {
			//     continue;
			// }

			let Some((idx, block)) = func.blocks.iter()
				.enumerate()
				.find(|(_, b)| b.label == blk.as_str())
				.map(|(i, b)| (i, b.clone()))
			 else {
				// We removed a forward block
				continue;
			};

			let fall_through = func.blocks.get(idx + 1).map(|b| b.label.to_string());
			let fall_through = fall_through.as_deref();

			// Fallthrough and branch go to the same place
			if let Some(loc) = block.ends_with_cond_branch() {
				if Some(loc) == fall_through {
					changed = true;
					to_jump.push((idx, Instruction::ImmJump(Loc(loc.to_string()))));
				}
			}

			// i (in "Engineering a Compiler" book pg. 548)
			if let Some(loc) = block.ends_with_jump() {
				// TODO: this should be ok... it was needed at one point
				// if loc.starts_with(".pre.") {
				//     continue;
				// }

				// j (in "Engineering a Compiler" book pg. 548)
				let Some(jump_to) = func.blocks.iter().find(|b| b.label == loc).cloned() else {
					// We removed a block (loc) this block (blk) has as an only child
					continue;
				};

				// The `all()` method defaults to true if no iteration happens
				if block.instructions.iter().all(|i| {
					matches!(
						i,
						Instruction::Skip(..) | Instruction::Label(..) | Instruction::Phi(..)
					)
				}) {
					changed = true;
					// println!("transfer {blk} to {loc}");
					replace_transfer(func, blk.as_str(), loc, idx);
					// TODO: also check the `jump_to` list for renamed labels
				}

				// Since this block ends with a jumpI (blk) and the location (loc) only
				// has one successor (so we aren't altering any dominator relations)
				// we remove the jump in blk and move `loc`'s instructions into `blk`
				if cfg_preds.get(&OrdLabel::new(loc)).map_or(false, |set| set.len() == 1) {
					changed = true;
					// println!("combine {loc} into {blk}");
					combine(func, loc, blk.as_str());
				}
				// The `all()` method defaults to true if no iteration happens!!
				if jump_to.instructions.iter().all(|i| {
					matches!(
						i,
						Instruction::Skip(..) | Instruction::Label(..) | Instruction::Phi(..)
					)
				}) {
					changed = true;
					println!("overwrite {blk} to {loc}");
				}
			}
		}

		#[allow(clippy::iter_with_drain)]
		for (idx, inst) in to_jump.drain(0..) {
			if let Some(cbr) = func.blocks[idx].instructions.last_mut() {
				*cbr = inst;
			}
		}

		let all: HashSet<_> = func.blocks.iter().map(|b| OrdLabel::new(&b.label)).collect();
		let used: HashSet<_> = reverse_postorder(&cfg_map, start).into_iter().cloned().collect();
		for unused in all.difference(&used) {
			changed = true;
			let pos = func.blocks.iter().position(|b| b.label == unused.as_str()).unwrap();
			func.blocks.remove(pos);
		}

		if changed {
			cfg_map = build_stripped_cfg(func);
		}
	}
}

pub fn build_stripped_cfg(func: &Function) -> HashMap<OrdLabel, BTreeSet<OrdLabel>> {
	let mut cfg: HashMap<_, BTreeSet<_>> = HashMap::default();

	let mut blocks = func.blocks.iter().enumerate().next().into_iter().collect::<VecDeque<_>>();
	'blk: while let Some((idx, block)) = blocks.pop_front() {
		let mut extend_blocks = vec![];
		let b_label = &block.label;
		for inst in &block.instructions {
			if inst.is_return() {
				cfg.entry(OrdLabel::from_known(b_label))
					.or_default()
					.insert(OrdLabel::from_known(".E_exit"));
				continue 'blk;
			}

			if let Some(label) = inst.uses_label() {
				let pos = func.blocks.iter().position(|b| b.label == label).unwrap();

				let unseen = cfg
					.entry(OrdLabel::from_known(b_label))
					.or_default()
					.insert(OrdLabel::from_known(label));
				// Skip the implicit branch to the block below the current one
				// since we found an unconditional jump.
				if inst.unconditional_jmp() {
					if unseen {
						blocks.push_back((pos, &func.blocks[pos]));
					}
					continue 'blk;
				} else if unseen {
					extend_blocks.push((pos, &func.blocks[pos]));
				}
			}
		}

		if let Some(next) = func.blocks.get(idx + 1) {
			let next_label = &next.label;
			cfg.entry(OrdLabel::from_known(b_label))
				.or_default()
				.insert(OrdLabel::from_known(next_label));
			extend_blocks.push((idx + 1, next));
			extend_blocks.reverse();
			blocks.extend(extend_blocks);
		}
	}
	cfg
}

fn combine(func: &mut Function, from: &str, into: &str) {
	let mut fr = None;
	let mut to = None;
	for (idx, blk) in func.blocks.iter().enumerate() {
		if blk.label == from {
			fr = Some(idx);
		}
		if blk.label == into {
			to = Some(idx);
		}
	}
	let Some(from) = fr else { return; };
	let Some(into) = to else { return; };

	let mut from_blk = func.blocks.remove(from);

	if let Some(instruction) = func.blocks[into].instructions.last_mut() {
		*instruction = Instruction::Skip(format!("{}", instruction));
	}

	func.blocks[into].instructions.extend(
		from_blk
			.instructions
			.extract_if(|i| !matches!(i, Instruction::Label(..) | Instruction::Frame { .. })),
	);
}

fn replace_transfer(func: &mut Function, to: &str, with: &str, idx: usize) {
	for blk in &mut func.blocks {
		if let Some(inst) = blk.instructions.last_mut() {
			if let Some(label) = inst.label_mut() {
				if label.as_str() == to {
					label.0 = with.to_string();
				}
			}
		}
	}
	if func.blocks[idx].label == to {
		func.blocks.remove(idx);
	}
}
