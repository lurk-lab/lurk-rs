// Initially taken from: rust-fil-proofs/storage-proofs-core/src/gadgets/
use crate::field::LurkField;
use bellpepper_core::LinearCombination;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::{AllocatedNum, Num},
    ConstraintSystem, SynthesisError, Variable,
};
use ff::PrimeField;

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
pub fn enforce_equal<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // debug_assert_eq!(a.get_value(), b.get_value());
    // a * 1 = b
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + b.get_variable(),
    );
}

/// Adds a constraint to CS, enforcing an equality relationship between an allocated number a and zero.
///
/// a == zero
#[allow(dead_code)]
pub(crate) fn enforce_equal_zero<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // debug_assert_eq!(a.get_value(), b.get_value());
    // a * 1 = zero
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc,
    );
}

/// Adds a constraint to CS, enforcing an equality relationship between an allocated number a and constant k.
///
/// a == k
#[allow(dead_code)]
pub(crate) fn enforce_equal_const<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    k: F,
    a: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // a * 1 = k
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + (k, CS::one()),
    );
}

/// Creates a linear combination representing the popcount (sum of one bits) of `v`.
pub(crate) fn popcount_lc<F: PrimeField, CS: ConstraintSystem<F>>(
    v: &[Boolean],
) -> LinearCombination<F> {
    v.iter().fold(LinearCombination::<F>::zero(), |acc, bit| {
        add_to_lc::<F, CS>(bit, acc, F::ONE)
    })
}

/// Adds a constraint to CS, enforcing that the addition of the allocated numbers in vector `v`
/// is equal to the value of the variable, `sum`.
pub(crate) fn popcount_equal<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    v: &[Boolean],
    sum: Variable,
) {
    let popcount = popcount_lc::<F, CS>(v);

    // popcount * 1 = sum
    cs.enforce(
        || "popcount",
        |_| popcount,
        |lc| lc + CS::one(),
        |lc| lc + sum,
    );
}

/// Adds a constraint to CS, enforcing that the addition of the allocated numbers in vector `v`
/// is equal to `one`.
///
/// summation(v) = one
#[inline]
#[allow(dead_code)]
pub(crate) fn enforce_popcount_one<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    v: &[Boolean],
) {
    popcount_equal(cs, v, CS::one())
}

pub(crate) fn add_to_lc<F: PrimeField, CS: ConstraintSystem<F>>(
    b: &Boolean,
    lc: LinearCombination<F>,
    scalar: F,
) -> LinearCombination<F> {
    match b {
        Boolean::Constant(c) => lc + (if *c { scalar } else { F::ZERO }, CS::one()),
        Boolean::Is(ref v) => lc + (scalar, v.get_variable()),
        Boolean::Not(ref v) => lc + (scalar, CS::one()) - (scalar, v.get_variable()),
    }
}

/// If premise is true, enforce `a` fits into 64 bits. It shows a non-deterministic
/// partial bit decomposition in order to constraint correct behavior.
pub(crate) fn implies_u64<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    let mut a_u64 = a.get_value().and_then(|a| a.to_u64()).unwrap_or(0);

    let mut bits: Vec<Boolean> = Vec::with_capacity(64);
    for i in 0..64 {
        let b = a_u64 & 1;
        let b_bool = Boolean::Is(AllocatedBit::alloc(
            ns!(cs, format!("b.{i}")),
            Some(b == 1),
        )?);
        bits.push(b_bool);

        a_u64 /= 2;
    }

    // premise -> a = sum(bits)
    implies_pack(ns!(cs, "u64 bit decomposition check"), premise, &bits, a);

    Ok(())
}

/// If premise is true, enforce v is the bit decomposition of num, therefore we have that 0 <= num < 2ˆ(sizeof(v)).
pub(crate) fn implies_pack<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    premise: &Boolean,
    v: &[Boolean],
    num: &AllocatedNum<F>,
) {
    let mut coeff = F::ONE;
    let mut pack = LinearCombination::<F>::zero();
    for b in v {
        pack = add_to_lc::<F, CS>(b, pack, coeff);
        coeff = coeff.double();
    }
    let diff = |_| pack - num.get_variable();
    let premise_lc = |_| premise.lc(CS::one(), F::ONE);
    let zero = |lc| lc;

    cs.enforce(|| "pack", diff, premise_lc, zero);
}

/// Adds a constraint to CS, enforcing a difference relationship between the allocated numbers a, b, and difference.
///
/// a - b = difference
pub(crate) fn enforce_difference<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    difference: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    //    difference = a-b
    // => difference + b = a
    // => (difference + b) * 1 = a
    cs.enforce(
        annotation,
        |lc| lc + difference.get_variable() + b.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable(),
    );
}

/// Compute difference and enforce it.
pub(crate) fn sub<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "sub_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.sub_assign(&b.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // a - b = res
    enforce_difference(&mut cs, || "subtraction constraint", a, b, &res);

    Ok(res)
}

/// Adds a constraint to CS, enforcing a linear relationship between the
/// allocated numbers a, b, c and num.  Namely, the linear equation
/// a * b + c = num is enforced.
///
/// a * b = num - c
pub(crate) fn enforce_product_and_sum<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    c: &AllocatedNum<F>,
    num: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // a * b = product
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + num.get_variable() - c.get_variable(),
    );
}

/// Adds a constraint to CS, enforcing a product relationship between the allocated numbers a, b, and product.
///
/// a * b = product
pub(crate) fn product<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    product: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // a * b = product
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + product.get_variable(),
    );
}

/// Compute product and enforce it.
pub(crate) fn mul<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "mul_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.mul_assign(&b.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // a * b = res
    product(&mut cs, || "multiplication constraint", a, b, &res);

    Ok(res)
}

pub(crate) fn div<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "div_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let inv = (b.get_value().ok_or(SynthesisError::AssignmentMissing)?).invert();

        if inv.is_some().into() {
            inv.map(|i| tmp.mul_assign(i));
            Ok(tmp)
        } else {
            Err(SynthesisError::DivisionByZero)
        }
    })?;

    // a = b * res
    product(&mut cs, || "division constraint", &res, b, a);

    Ok(res)
}

pub(crate) fn invert<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let inv = AllocatedNum::alloc(cs.namespace(|| "invert"), || {
        let inv = (a.get_value().ok_or(SynthesisError::AssignmentMissing)?).invert();

        let inv_opt: Option<_> = inv.into();
        inv_opt.ok_or(SynthesisError::DivisionByZero)
    })?;

    // inv * a = 1
    cs.enforce(
        || "inversion",
        |lc| lc + inv.get_variable(),
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one(),
    );

    Ok(inv)
}

/// Select the nth element of `from`, where `path_bits` represents n, least-significant bit first.
/// The returned result contains the selected element, and constraints are enforced.
/// `from.len()` must be a power of two.
#[allow(dead_code)]
pub(crate) fn select<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    from: &[AllocatedNum<F>],
    path_bits: &[Boolean],
) -> Result<AllocatedNum<F>, SynthesisError> {
    let pathlen = path_bits.len();
    assert_eq!(1 << pathlen, from.len());

    let mut state = from.to_vec();
    let mut half_size = from.len() / 2;

    // We reverse the path bits because the contained algorithm consumes most significant bit first.
    for (i, bit) in path_bits.iter().rev().enumerate() {
        let mut new_state = Vec::with_capacity(half_size);
        for j in 0..half_size {
            new_state.push(pick(
                cs.namespace(|| format!("pick {i}, {j}")),
                bit,
                &state[half_size + j],
                &state[j],
            )?);
        }
        state = new_state;
        half_size /= 2;
    }

    Ok(state.remove(0))
}

/// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub(crate) fn pick<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let c = AllocatedNum::alloc(cs.namespace(|| "pick result"), || {
        if condition
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            Ok(a.get_value().ok_or(SynthesisError::AssignmentMissing)?)
        } else {
            Ok(b.get_value().ok_or(SynthesisError::AssignmentMissing)?)
        }
    })?;

    // Constrain (b - a) * condition = (b - c), ensuring c = a iff
    // condition is true, otherwise c = b.
    cs.enforce(
        || "pick",
        |lc| lc + b.get_variable() - a.get_variable(),
        |_| condition.lc(CS::one(), F::ONE),
        |lc| lc + b.get_variable() - c.get_variable(),
    );

    Ok(c)
}

/// Takes two numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub(crate) fn pick_const<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    condition: &Boolean,
    a: F,
    b: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let c = AllocatedNum::alloc(cs.namespace(|| "pick result"), || {
        if condition
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            Ok(a)
        } else {
            Ok(b)
        }
    })?;

    // Constrain (b - a) * condition = (b - c), ensuring c = a iff
    // condition is true, otherwise c = b.
    cs.enforce(
        || "pick",
        |lc| lc + (b, CS::one()) - (a, CS::one()),
        |_| condition.lc(CS::one(), F::ONE),
        |lc| lc + (b, CS::one()) - c.get_variable(),
    );

    Ok(c)
}

/// Convert from Boolean to AllocatedNum.
#[allow(dead_code)]
pub(crate) fn boolean_to_num<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bit: &Boolean,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let num = AllocatedNum::alloc(cs.namespace(|| "Allocate num"), || {
        if bit.get_value().ok_or(SynthesisError::AssignmentMissing)? {
            Ok(F::ONE)
        } else {
            Ok(F::ZERO)
        }
    })?;

    // Constrain (bit) * 1 = num, ensuring bit = num
    cs.enforce(
        || "Bit is equal to Num",
        |_| bit.lc(CS::one(), F::ONE),
        |lc| lc + CS::one(),
        |lc| lc + num.get_variable(),
    );

    Ok(num)
}

/// This could now use alloc_is_zero to avoid duplication.
pub fn alloc_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value().and_then(|x| b.get_value().map(|y| x == y));

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), equal)?;

    // result * (a - b) = 0
    // This means that at least one of result or a - b is zero.
    cs.enforce(
        || "result or diff is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc,
    );

    // Inverse of `a - b`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let tmp0 = a_val - b_val;
            let tmp1 = tmp0.invert();

            if tmp1.is_some().into() {
                Ok(tmp1.unwrap())
            } else {
                Ok(F::ONE)
            }
        },
    )?;

    // (a - b + result) * q = 1.
    // This enforces that diff and result are not both 0.
    cs.enforce(
        || "(a - b + result) * q = 1",
        |lc| lc + a.get_variable() - b.get_variable() + result.get_variable(),
        |lc| lc + q,
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `diff` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `diff` is 0.
    // `Diff` is 0 iff `a == b`.
    // Therefore, `result = (a == b)`.

    Ok(Boolean::Is(result))
}

/// Like `alloc_equal`, but with second argument a constant.
pub(crate) fn alloc_equal_const<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: F,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value().map(|x| x == b);

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = a.get_value().map(|x| x - b); //sub(cs.namespace(|| "a - b"), a, b)?;

    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), equal)?;

    // result * diff = 0
    // This means that at least one of result or diff is zero.
    cs.enforce(
        || "result or diff is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + a.get_variable() - (b, CS::one()),
        |lc| lc,
    );

    // Inverse of `diff`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            let tmp0 = diff.ok_or(SynthesisError::AssignmentMissing)?;
            let tmp1 = tmp0.invert();

            if tmp1.is_some().into() {
                Ok(tmp1.unwrap())
            } else {
                Ok(F::ONE)
            }
        },
    )?;

    // ((a - b) + result) * q = 1.
    // This enforces that diff (a - b) and result are not both 0.
    cs.enforce(
        || "((a-b) + result) * q = 1",
        |lc| lc + a.get_variable() - (b, CS::one()) + result.get_variable(),
        |lc| lc + q,
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `diff` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `diff` is 0.
    // `Diff` is 0 iff `a == b`.
    // Therefore, `result = (a == b)`.

    Ok(Boolean::Is(result))
}

/// Allocate a Boolean which is true if and only if `x` is zero.
pub(crate) fn alloc_is_zero<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: CS,
    x: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    alloc_num_is_zero(cs, &Num::from(x.clone()))
}

/// Allocate a Boolean which is true if and only if `num` is zero.
pub(crate) fn alloc_num_is_zero<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    num: &Num<F>,
) -> Result<Boolean, SynthesisError> {
    let num_value = num.get_value();
    let x = num_value.unwrap_or(F::ZERO);
    let is_zero = num_value.map(|n| n == F::ZERO);

    // result = (x == 0)
    let result = AllocatedBit::alloc(cs.namespace(|| "x = 0"), is_zero)?;

    // result * x = 0
    // This means that at least one of result or x is zero.
    cs.enforce(
        || "result or x is 0",
        |lc| lc + result.get_variable(),
        |_| num.lc(F::ONE),
        |lc| lc,
    );

    // Inverse of `x`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            let tmp = x.invert();
            if tmp.is_some().into() {
                Ok(tmp.unwrap())
            } else {
                Ok(F::ONE)
            }
        },
    )?;

    // (x + result) * q = 1.
    // This enforces that x and result are not both 0.
    cs.enforce(
        || "(x + result) * q = 1",
        |_| num.lc(F::ONE) + result.get_variable(),
        |lc| lc + q,
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `x` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `x` is 0.

    Ok(Boolean::Is(result))
}

/// Takes a boolean premise and a function that produces a `LinearCombination` (with same specification as `enforce`).
/// Enforces the constraint that if `premise` is true, then the resulting linear combination evaluates to one.
pub(crate) fn enforce_implication_lc<
    CS: ConstraintSystem<F>,
    F: PrimeField,
    L: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
>(
    mut cs: CS,
    premise: &Boolean,
    implication_lc: L,
) {
    let premise_b = premise.lc(CS::one(), F::ONE);
    let premise_c = premise_b.clone();

    // implication * premise = premise
    cs.enforce(
        || "implication",
        implication_lc,
        |_| premise_b,
        |_| premise_c,
    );
}

/// Takes a boolean premise and a function that produces a `LinearCombination` (with same specification as `enforce`).
/// Enforces the constraint that if `premise` is true, then the resulting linear combination evaluates to zero.
pub(crate) fn enforce_implication_lc_zero<
    CS: ConstraintSystem<F>,
    F: PrimeField,
    L: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
>(
    mut cs: CS,
    premise: &Boolean,
    implication_lc: L,
) {
    let premise_a = premise.lc(CS::one(), F::ONE);
    // premise * implication = zero
    cs.enforce(|| "implication", |_| premise_a, implication_lc, |lc| lc);
}

/// Adds a constraint to CS, enforcing that the number of true bits in `Boolean` vector `v`
/// is equal to one, if the premise is true.
///
/// summation(v) = one (if premise)
pub(crate) fn enforce_selector_with_premise<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    premise: &Boolean,
    v: &[Boolean],
) {
    let popcount = popcount_lc::<F, CS>(v);

    enforce_implication_lc(cs, premise, |_| popcount);
}

/// Enforce `premise` implies `implication`.
#[allow(dead_code)]
pub(crate) fn enforce_implication<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: CS,
    premise: &Boolean,
    implication: &Boolean,
) {
    enforce_implication_lc(cs, premise, |_|
                           // One if implication is true, zero otherwise.
                           implication.lc(CS::one(), F::ONE));
}

/// Enforce equality of two allocated numbers given an implication premise
pub(crate) fn implies_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) {
    enforce_implication_lc_zero(cs, premise, |lc| {
        // Zero iff `a` == `b`.
        lc + a.get_variable() - b.get_variable()
    })
}

/// Enforce equality of an allocated number and a constant given an implication premise
pub(crate) fn implies_equal_const<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: F,
) {
    enforce_implication_lc_zero(cs, premise, |lc| lc + a.get_variable() - (b, CS::one()))
}

/// Enforce inequality of two allocated numbers given an implication premise
#[allow(dead_code)]
pub(crate) fn implies_unequal<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    // We know that `a != b` iff `a-b` has an inverse, i.e. that there exists
    // `c` such that `c * (a-b) = 1`. Thus, we can add the constraint that there
    // must exist `c` such that `c * (a-b) = premise`, enforcing the difference
    // only when `premise = 1`; otherwise the constraint is trivially satisfied
    // for `c = 0`
    let q = cs.alloc(
        || "q",
        || {
            let premise = premise
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            if premise {
                let a = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let b = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let inv = (a - b).invert();
                if inv.is_some().into() {
                    Ok(inv.unwrap())
                } else {
                    Ok(F::ZERO)
                }
            } else {
                Ok(F::ZERO)
            }
        },
    )?;
    let maybe_inverse = |lc| lc + q;
    let implication_lc = |lc| lc + a.get_variable() - b.get_variable();
    let premise = |_| premise.lc(CS::one(), F::ONE);

    cs.enforce(|| "implication", maybe_inverse, implication_lc, premise);
    Ok(())
}

/// Enforce inequality of two allocated numbers given an implication premise
pub(crate) fn implies_unequal_const<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: F,
) -> Result<(), SynthesisError> {
    // We know that `a != b` iff `a-b` has an inverse, i.e. that there exists
    // `c` such that `c * (a-b) = 1`. Thus, we can add the constraint that there
    // must exist `c` such that `c * (a-b) = premise`, enforcing the difference
    // only when `premise = 1`; otherwise the constraint is trivially satisfied
    // for `c = 0`
    let q = cs.alloc(
        || "q",
        || {
            let premise = premise
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            if premise {
                let a = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let inv = (a - b).invert();
                if inv.is_some().into() {
                    Ok(inv.unwrap())
                } else {
                    Ok(F::ZERO)
                }
            } else {
                Ok(F::ZERO)
            }
        },
    )?;
    let maybe_inverse = |lc| lc + q;
    let implication_lc = |lc| lc + a.get_variable() - (b, CS::one());
    let premise = |_| premise.lc(CS::one(), F::ONE);

    cs.enforce(|| "implication", maybe_inverse, implication_lc, premise);
    Ok(())
}

/// Enforce equality of two allocated numbers given an implication premise
#[allow(dead_code)]
pub(crate) fn implies_equal_zero<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
) {
    enforce_implication_lc_zero(cs, premise, |lc| lc + a.get_variable())
}

/// Use DeMorgan to constrain or.
pub(crate) fn or<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::not(&Boolean::and(
        cs.namespace(|| "not and (not a) (not b)"),
        &Boolean::not(a),
        &Boolean::not(b),
    )?))
}

#[allow(dead_code)]
pub(crate) fn must_be_simple_bit(x: &Boolean) -> AllocatedBit {
    match x {
        Boolean::Constant(_) => panic!("Expected a non-constant Boolean."),
        Boolean::Is(b) => b.clone(),
        Boolean::Not(_) => panic!("Expected a non-negated Boolean."),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::Field;
    use halo2curves::bn256::Fr;

    #[test]
    fn edge_enforce_implication_lc() {
        ////////////////////////////////////////////
        // Big lc
        // an lc > 1 should fail if premise is true.
        ////////////////////////////////////////////

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut test_lc_big = LinearCombination::zero();
        test_lc_big = test_lc_big + (Fr::ONE + Fr::ONE, TestConstraintSystem::<Fr>::one());

        // Allocate premise boolean.
        let premise_true = Boolean::from(
            AllocatedBit::alloc(cs.namespace(|| "premise_true"), Some(true)).expect("alloc failed"),
        );

        // Execute the function under test.
        enforce_implication_lc(
            cs.namespace(|| "enforce_implication_lc_big"),
            &premise_true,
            |_| test_lc_big.clone(),
        );

        assert!(!cs.is_satisfied());

        ////////////////////////////////////////////

        let mut cs = TestConstraintSystem::<Fr>::new();
        // an lc > 1 should pass if premise is false.
        // Allocate premise boolean.
        let premise_false = Boolean::from(
            AllocatedBit::alloc(cs.namespace(|| "premise_false"), Some(false))
                .expect("alloc failed"),
        );

        // Execute the function under test.
        enforce_implication_lc(
            cs.namespace(|| "enforce_implication_lc_big_with_false"),
            &premise_false,
            |_| test_lc_big,
        );

        assert!(cs.is_satisfied());

        ///////////////////////////////////////////////////////////////////////
        // type constraints: lcs not made of booleans may incidentally pass. //
        ///////////////////////////////////////////////////////////////////////
        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut test_lc_arb_num = LinearCombination::zero();

        // Allocate a few numbers. Here TWO_INV + TWO_INV = ONE
        let anum1 = AllocatedNum::alloc_infallible(cs.namespace(|| "num1"), || Fr::TWO_INV);
        let anum2 = AllocatedNum::alloc_infallible(cs.namespace(|| "num2"), || Fr::TWO_INV);

        // Add them to the lc
        test_lc_arb_num = test_lc_arb_num + (Fr::ONE, anum1.get_variable());
        test_lc_arb_num = test_lc_arb_num + (Fr::ONE, anum2.get_variable());

        // Execute the function under test.
        enforce_implication_lc(
            cs.namespace(|| "enforce_implication_lc_arb_num"),
            &premise_true,
            |_| test_lc_arb_num,
        );

        assert!(cs.is_satisfied());
    }

    #[test]
    fn edge_enforce_implication_lc_zero() {
        ////////////////////////////////////////////
        // Big lc
        // an lc > 1 should fail if premise is true.
        ////////////////////////////////////////////

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut test_lc_big = LinearCombination::zero();
        test_lc_big = test_lc_big + (Fr::ONE + Fr::ONE, TestConstraintSystem::<Fr>::one());

        let test_lc_one = LinearCombination::zero() + TestConstraintSystem::<Fr>::one();

        // Allocate premise boolean.
        let premise_true = Boolean::from(
            AllocatedBit::alloc(cs.namespace(|| "premise_true"), Some(true)).expect("alloc failed"),
        );

        // Execute the function under test.
        enforce_implication_lc_zero(
            cs.namespace(|| "enforce_implication_lc_big"),
            &premise_true,
            |_| test_lc_big.clone(),
        );

        assert!(!cs.is_satisfied());

        ////////////////////////////////////////////

        ////////////////////////////////////////////
        // One lc
        // an lc = 1 should fail if premise is true.
        ////////////////////////////////////////////

        let mut cs = TestConstraintSystem::<Fr>::new();

        // Allocate premise boolean.
        let premise_true = Boolean::from(
            AllocatedBit::alloc(cs.namespace(|| "premise_true"), Some(true)).expect("alloc failed"),
        );

        // Execute the function under test.
        enforce_implication_lc_zero(
            cs.namespace(|| "enforce_implication_lc_one"),
            &premise_true,
            |_| test_lc_one.clone(),
        );

        assert!(!cs.is_satisfied());

        ////////////////////////////////////////////

        let mut cs = TestConstraintSystem::<Fr>::new();

        // an lc != 0 should pass if premise is false.
        // Allocate premise boolean.
        let premise_false = Boolean::from(
            AllocatedBit::alloc(cs.namespace(|| "premise_false"), Some(false))
                .expect("alloc failed"),
        );

        // Execute the function under test.
        enforce_implication_lc_zero(
            cs.namespace(|| "enforce_implication_lc_big_with_false"),
            &premise_false,
            |_| test_lc_big,
        );

        assert!(cs.is_satisfied());

        ///////////////////////////////////////////////////////////////////////
        // type constraints: lcs not made of booleans may incidentally pass. //
        ///////////////////////////////////////////////////////////////////////

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut test_lc_arb_num = LinearCombination::zero();

        // Allocate a number that is zero, but not a Boolean.
        let anum1 = AllocatedNum::alloc_infallible(cs.namespace(|| "num1"), || Fr::ZERO);

        // Add it to the lc
        test_lc_arb_num = test_lc_arb_num + (Fr::ONE, anum1.get_variable());

        // Execute the function under test.
        enforce_implication_lc_zero(
            cs.namespace(|| "enforce_implication_lc_arb_num"),
            &premise_true,
            |_| test_lc_arb_num,
        );

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_implies_u64_negative_edge_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let alloc_num = AllocatedNum::alloc(ns!(cs, "num"), || {
            // Edge case: 2ˆ64 = 18446744073709551616
            Ok(Fr::from_str_vartime("18446744073709551616").unwrap())
        })
        .unwrap();

        let t = Boolean::Constant(true);
        implies_u64(ns!(cs, "enforce u64"), &t, &alloc_num).unwrap();
        assert!(!cs.is_satisfied());
    }
}
