use std::{
	collections::{BTreeSet, HashMap, VecDeque},
	ops::Range, fmt::Debug,
};

use crate::{
	iloc::{Block, Instruction, Operand, Reg},
	ssa::DominatorTree,
};

#[derive(Clone, Debug)]
pub struct RenameMeta {
	stack: VecDeque<usize>,
	last_name: isize,
}
impl Default for RenameMeta {
	fn default() -> Self { Self { stack: VecDeque::from([]), last_name: -1 } }
}

fn new_name(reg: Reg, meta: &mut HashMap<Reg, RenameMeta>) {
	let m = meta.entry(reg).or_default();
	m.last_name += 1;
	m.stack.push_front(m.last_name as usize);
}

fn rewrite_name(reg: &mut Reg, meta: &mut HashMap<Reg, RenameMeta>) {
	if *reg == Reg::Var(0) {
		*reg = Reg::Phi(0, 0);
		return;
	}
	let m = meta.entry(*reg).or_default();
	let phi_id = m.stack.front().copied().unwrap_or_else(|| panic!("{:?}", reg));
	reg.as_phi(phi_id);
}

pub type ScopedExprTree = VecDeque<HashMap<(Operand, Option<Operand>, String), (Reg, usize)>>;

pub fn dom_val_num(
	blks: &mut [Block],
	blk_idx: usize,
	meta: &mut HashMap<Reg, RenameMeta>,
	dtree: &DominatorTree,
	expr_tree: &mut ScopedExprTree,
) {
	let blk_label = blks[blk_idx].label.clone();

	expr_tree.push_back(HashMap::new());
	for op in &blks[blk_idx].instructions {
		// Remove redundant/meaningless phi instructions
		if let Instruction::Phi(r, set, subscript) = op {
			// We need to update the phi before we check it, Carr does this but all papers
			// say to update only after we know it is a unique phi, loops may ruin this???
			new_name(*r, meta);
			// No more processing for Phi nodes
			continue;
		}
	}

	let mut dead = BTreeSet::new();
	// We need to iter all instructions (the frame instruction was being skipped) so don't
	// use the phi range end as a start
	for (inst_idx, op) in blks[blk_idx].instructions.iter_mut().enumerate() {
		let (mut a, mut b) = op.operands_mut();
		if let Some(a) = a.as_mut() {
			rewrite_name(a, meta);
		}
		if let Some(b) = b.as_mut() {
			rewrite_name(b, meta);
		}

		// Rename registers that don't fit neatly into the operands category
		match op {
			Instruction::Call { args, .. } => {
				for arg in args {

					rewrite_name(arg, meta);
				}
			}
			Instruction::ImmCall { args, ret, .. } | Instruction::ImmRCall { args, ret, .. } => {
				for arg in args {
					let m = meta.entry(*arg).or_default();
					rewrite_name(arg, meta);
				}
			}
			Instruction::Store { dst, .. }
			| Instruction::StoreAdd { dst, .. }
			| Instruction::StoreAddImm { dst, .. } => {
				let m = meta.entry(*dst).or_default();
				rewrite_name(dst, meta);
			}
			_ => {}
		}

		if let (Some(a), b) = op.operands() {
			let is_expr = op.is_tmp_expr();
			let is_commutative = op.is_commutative();
			let inst_name = op.inst_name().to_string();

			let expr = (a.clone(), b.clone(), inst_name.clone());
			if let Some((prev_reg, subs)) = expr_tree.iter().rev().find_map(|map| map.get(&expr)) {
				if !is_expr {
					// We need all registers to be converted
					if let Some(dst) = op.target_reg() {
						// When we see a new definition of a register we increment it's phi value
						new_name(*dst, meta);
					}
					continue;
				}

				if let Some(dst) = op.target_reg() {
					// If the expression has been seen before and is equivalently ssa
					// numbered we know it is an equal expression so we can reuse the
					// ssa value number for this dst register
					let m = meta.entry(*dst).or_default();
					m.stack.push_front(*subs);
					// Because we didn't keep track of the actual register we could
					// remove `loadI`s that loaded the same value to a different destination
					if prev_reg == dst {
						dead.insert(inst_idx);
					}
				}

			} else if let Some(dst) = op.target_reg() {
				// When we see a new definition of a register we increment it's phi value
				new_name(*dst, meta);

				if is_expr {
					let m = meta.get(dst).unwrap();
					let expr_tree = expr_tree.back_mut().unwrap();
					expr_tree.insert(expr, (*dst, *m.stack.front().unwrap()));

					if is_commutative {
						expr_tree.insert(
							(b.clone().unwrap(), Some(a.clone()), inst_name),
							(*dst, *m.stack.front().unwrap()),
						);
					}
				}
			}
		// Non-ssa expression instruction
		// There are a few instructions that have no operands but have registers
		} else if let Some(dst) = op.target_reg() {
			// When we see a new definition of a register we increment it's phi value
			new_name(*dst, meta);
		} else if let Instruction::Frame {  params, .. } = op {
			for dst in params { new_name(*dst, meta); }
		}
	}

	let empty = BTreeSet::new();
	for blk in dtree.cfg_succs_map.get(blk_label.as_str()).unwrap_or(&empty) {
		// TODO: make block -> index map
		let idx = blks.iter().position(|b| b.label == blk.as_str()).unwrap();
		for phi in &mut blks[idx].instructions {
			if let Instruction::Phi(r, set, subscript) = phi {
				// When looking forward into successor blocks we transfer the current phi
				// number since we know this is the correct number to cross the block
				//
				// We are adding the number to the set of incoming subscripts that makes
				// up the phi
				let m = meta.entry(*r).or_default();
				if let Some(&i) = m.stack.front() {
					set.insert(i);
				}
			}
		}
	}

	// This is what drives the rename algorithm
	for blk in dtree.dom_tree.get(blk_label.as_str()).unwrap_or(&empty) {
		// println!("{blk_label} -> {blk}");

		// TODO: make block -> index map
		let idx = blks.iter().position(|b| b.label == blk.as_str()).unwrap();
		dom_val_num(blks, idx, meta, dtree, expr_tree);
	}

	for (i, op) in blks[blk_idx].instructions.iter_mut().enumerate().rev() {
		if let Some(dst) = op.target_reg_mut() {
			if let Some(meta) = meta.get_mut(dst) {
				let subscript = meta.stack.pop_front().unwrap();

				// println!("{blk_label} {:?} -> {subscript}", dst);

				if dead.contains(&i) {
					*op = Instruction::Skip(format!("[ssadbvn] {}", op));
				} else {
					dst.as_phi(subscript);
				}
			}
		} else if let Instruction::Frame { params, .. } = op {
			// There is no check for `dead` since a frame instruction can't ever be unused code
			for dst in params {
				if let Some(meta) = meta.get_mut(dst) {
					let subscript = meta.stack.pop_front().unwrap();
					dst.as_phi(subscript);
				}
			}
		}
	}
	for op in &mut blks[blk_idx].instructions {
		if let Instruction::Phi(r, set, subs) = op {
			if let Some(meta) = meta.get_mut(r) {
				let subscript = meta.stack.pop_front().unwrap();
				subs.replace(subscript);
			} else { unreachable!() }
		}
	}

	// Pop scope since we are leaving
	expr_tree.pop_back();

}
