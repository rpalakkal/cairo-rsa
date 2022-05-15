#based on https://github.com/bellissimogiorno/cairo-integer-types/int_unbounded
# https://github.com/starkware-libs/cairo-lang/blob/master/src/starkware/cairo/common/math.cairo
from starkware.cairo.common.math import assert_nn_le, assert_not_zero, assert_in_range, unsigned_div_rem
# https://github.com/starkware-libs/cairo-lang/blob/master/src/starkware/cairo/common/math_cmp.cairo
from starkware.cairo.common.math_cmp import is_nn
from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.registers import get_label_location
from starkware.cairo.common.memcpy import memcpy


# Some constants
# The file should be parametric over values for BIT_LENGTH up to 125
const BIT_LENGTH = 125
const SHIFT = 2 ** 125
const EON = -1
# const NEG = -2

# Gather everything into a namespace for easier import
namespace biguint:
    # DATATYPE (STRUCT)

    # Represents an unbounded unsigned integer (a natural number) as a pointer to the integer in memory,
    # represented base SHIFT as an EON-terminated list of felts in [0,SHIFT) with least significant digit first.
    # For example: 1 is represented as `[1,EON]` and 0 is represented as `[EON]`.
    struct BigUint:
        member ptr : felt*
    end

    # Verifies that `a` points to a properly-formatted biguint
    func num_check_helper{range_check_ptr}(a : BigUint, previous_digit : felt):
        # If we terminate here, make sure the previous digit was not 0, e.g. [0,EON] is considered invalid.
        if [a.ptr] == EON:
            assert_not_zero(previous_digit)
            return ()
        else:
            assert_in_range([a.ptr], 0, SHIFT)
            num_check_helper(BigUint(a.ptr + 1), [a.ptr])
            return ()
        end
    end

    # A valid biguint is either
    # * [EON] (representing zero) or
    # * some least dignificant digit followed by a valid biguint.
    func num_check{range_check_ptr}(a : BigUint):
        if [a.ptr] != EON:
            assert_in_range([a.ptr], 0, SHIFT)
            num_check_helper(BigUint(a.ptr + 1), [a.ptr])
            return ()
        end
        return ()
    end

    # Helpful for testing
    func id(a : BigUint) -> (a : BigUint):
        return (a=a)
    end

    # Calculates how many digits a number has, in modulo-SHIFT representation.
    # E.g. [0, 1, -1] has two digits and represents the number SHIFT.
    func len(a : BigUint) -> (res : felt):
        if [a.ptr] == EON:
            # a is zero, nothing more to check
            return (0)
        else:
            let (tail_len) = len(BigUint(a.ptr + 1))
            return (res=1 + tail_len)
        end
    end

    # EQUALITY

    # Verifies whether `a` denotes zero
    # Returns 0 if zero and 1 if nonzero
    func is_not_zero(a : BigUint) -> (res : felt):
        if [a.ptr] == EON:
            return (0)
        else:
            return (1)
        end
    end

    # Verifies that `a` and `b` point to arithmetically equal biguints.
    # Returns 0 if non-equal and 1 if equal
    # Could be trivially implemented using compare, but the version below should be quicker and it does not require the range_check builtin
    func is_eq(a : BigUint, b : BigUint) -> (res : felt):
        if [a.ptr] == EON:
            if [b.ptr] == EON:
                # both a and b are zero, thus equal
                return (1)
            else:
                # a is 0 and b isn't, thus they are not equal
                return (0)
            end
        else:
            # least significant digits equal?  Proceed to next digit
            if [a.ptr] == [b.ptr]:
                let (res) = is_eq(BigUint(a.ptr + 1), BigUint(b.ptr + 1))
                return (res)
            else:
                # lsd are non-equal?  Return 0.
                return (0)
            end
        end
    end

    # Assert that `a` and `b` point to arithmetically equal biguints.
    # Fails if they don't
    func assert_eq(a : BigUint, b : BigUint):
        if ([a.ptr] - EON) + ([b.ptr] - EON) == 0:
            # both a and b are zero, thus equal
            return ()
        end
        # least significant digits equal?  Proceed to next digit
        if [a.ptr] == [b.ptr]:
            assert_eq(BigUint(a.ptr + 1), BigUint(b.ptr + 1))
            return ()
        else:
            assert 1 = 0
            return ()
        end
    end

    # COMPARISON

    # utility function designed to be called on two biguints of equal lengh
    # returns -1 if a<b, 0 if a=b, +1 if a>b
    func compare_helper{range_check_ptr}(a_ptr : felt*, b_ptr : felt*, len) -> (res : felt):
        if len == -1:
            # no digits left to compare.  a and b are equal
            return (0)
        end
        # is the most significant digit of a less than that of b?
        # e.g. if a = 2 and b = 2 then b-a-1 = -1.
        let (a_leading_digit_lt_b_leading_digit) = is_nn([b_ptr + len] - [a_ptr + len] - 1)
        if a_leading_digit_lt_b_leading_digit == 1:
            return (-1)
        end
        # is the most significant digit of b less than that of a?
        let (b_leading_digit_lt_a_leading_digit) = is_nn([a_ptr + len] - [b_ptr + len] - 1)
        if b_leading_digit_lt_a_leading_digit == 1:
            return (1)
        end
        # most significant digits are equal.  Must go to less significant digit
        return compare_helper(a_ptr, b_ptr, len - 1)
    end

    # Compare two biguints
    # returns -1 if a<b, 0 if a=b, +1 if a>b
    func compare{range_check_ptr}(a : BigUint, b : BigUint) -> (res : felt):
        alloc_locals
        let (a_len) = len(a)
        let (b_len) = len(b)
        let (is_a_shorter_than_b) = is_nn(b_len - a_len - 1)  # e.g. if b_len = a_len = 2 then (b_len - a_len - 1 = -1, which is negative)
        if is_a_shorter_than_b == 1:
            return (-1)
        end
        let (is_b_shorter_than_a) = is_nn(a_len - b_len - 1)  # e.g. if a_len = b_len = 2 then (a_len - b_len - 1 = -1, which is negative)
        if is_b_shorter_than_a == 1:
            return (1)
        end
        # Looks like a and b have equal digit length.
        # Time to pull out our lexicographic order!
        return compare_helper(a.ptr, b.ptr, a_len)
    end

    func is_lt{range_check_ptr}(a : BigUint, b : BigUint) -> (res : felt):
        alloc_locals
        let (cmp) = compare(a, b)
        # cmp = -1 if a<b, 0 if a=b, +1 if a>b
        # ((cmp - 1) * cmp) / 2 = 1 if cmp=-1, and = 0 if cmp=0 or 1.
        return (((cmp - 1) * cmp) / 2)
    end

    func is_le{range_check_ptr}(a : BigUint, b : BigUint) -> (res : felt):
        alloc_locals
        let (cmp) = compare(b, a)
        # cmp = -1 if a>b, 0 if b=a, +1 if a<b
        # 1 - (((cmp - 1) * cmp) / 2) = 0 if cmp=-1,  = 1 if cmp=0 or 1.
        return (1 - (((cmp - 1) * cmp) / 2))
    end

    # ARITHMETIC

    func assert_sum_eq_with_carry{range_check_ptr}(
            a_digits_ptr : felt*, b_digits_ptr : felt*, res_digits_ptr : felt*, last_carry : felt):
        alloc_locals
        local a_digit : felt
        local a_continues : felt
        local b_digit : felt
        local b_continues : felt

        # has a finished?
        if [a_digits_ptr] == EON:
            a_digit = 0
            a_continues = 0
        else:
            a_digit = [a_digits_ptr]
            a_continues = 1
        end
        # has b finished?
        if [b_digits_ptr] == EON:
            b_digit = 0
            b_continues = 0
        else:
            b_digit = [b_digits_ptr]
            b_continues = 1
        end
        # Have a and b finished _and_ there's no carry?
        if a_continues + b_continues + last_carry == 0:
            # Then res should be finished.  Check for EON marker and return
            assert [res_digits_ptr] = EON
            return ()
        end
        # If we get to here, then a, b, or last_carry contribute some non-zero component.
        # Check 0 <= res_digit < SHIFT
        assert_nn_le([res_digits_ptr], SHIFT - 1)
        # a_digit + b_digit + last_carry = [res.ptr] + next_carry * SHIFT
        local next_carry = (a_digit + b_digit + last_carry - [res_digits_ptr]) / SHIFT
        # Check next_carry is 0 or 1
        assert next_carry * next_carry = next_carry
        return assert_sum_eq_with_carry(
            a_digits_ptr + a_continues, b_digits_ptr + b_continues, res_digits_ptr + 1, next_carry)
    end

    func add{range_check_ptr}(a : BigUint, b : BigUint) -> (res : BigUint):
        alloc_locals
        # guess a result
        local res_ptr : felt*
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates res_ptr with correct result
            from biguint_tools import peek_one_num_from, num_add
            a = peek_one_num_from(memory, ids.a.ptr)
            b = peek_one_num_from(memory, ids.b.ptr)
            a_plus_b = num_add(a, b)
            ids.res_ptr = segments.gen_arg(a_plus_b)
        %}
        # Check res_ptr (points to a) biguint
        num_check(BigUint(res_ptr))
        # check res = a + b
        assert_sum_eq_with_carry(a.ptr, b.ptr, res_ptr, 0)
        # Lucky guess!  Return the result
        return (BigUint(res_ptr))
    end

    # Calculates a - b.
    # If a >= b returns (a-b,  1)
    # If a  < b returns (b-a, -1)
    func sub{range_check_ptr}(a : BigUint, b : BigUint) -> (res : BigUint, sign : felt):
        alloc_locals
        # guess a result
        local res_ptr : felt*
        local sign : felt
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates res_ptr with correct result
            from biguint_tools import peek_one_num_from, num_sub
            a = peek_one_num_from(memory, ids.a.ptr)
            b = peek_one_num_from(memory, ids.b.ptr)
            (sign, res) = num_sub(a, b)
            ids.res_ptr = segments.gen_arg(res)
            ids.sign = (sign % PRIME)
        %}
        # expect sign to be 1 or -1
        assert sign * sign = 1
        # Check res_ptr (points to a) biguint
        num_check(BigUint(res_ptr))
        if sign == 1:
            # Expect res + b = a
            assert_sum_eq_with_carry(res_ptr, b.ptr, a.ptr, 0)
            return (res=BigUint(res_ptr), sign=1)
        else:
            # Expect -res + b = a, so res + a = b
            assert_sum_eq_with_carry(res_ptr, a.ptr, b.ptr, 0)
            return (res=BigUint(res_ptr), sign=-1)
        end
    end

    # multiplies a biguint by a single nonzero digit (helper function)
    func mul_by_nonzero_digit_helper{range_check_ptr}(
            a_digits_ptr : felt*, b : felt, res_digits_ptr : felt*, last_carry : felt):
        alloc_locals
        local a_digit : felt
        local a_continues : felt
        # has a finished?
        if [a_digits_ptr] == EON:
            a_digit = 0
            a_continues = 0
        else:
            a_digit = [a_digits_ptr]
            a_continues = 1
        end
        # Has a finished and there's no carry?
        if a_continues + last_carry == 0:
            # Then res should be finished.  Check for EON marker and return
            assert [res_digits_ptr] = EON
            return ()
        end
        # If we get to here, then a or last_carry contribute some non-zero component.
        # Check 0 <= res_digit < SHIFT
        assert_nn_le([res_digits_ptr], SHIFT - 1)
        local next_carry = (a_digit * b + last_carry - [res_digits_ptr]) / SHIFT
        # Check 0 <= next_carry < SHIFT
        assert_nn_le(next_carry, SHIFT - 1)
        # a_digit * b + last_carry = [res.ptr] + next_carry * SHIFT
        return mul_by_nonzero_digit_helper(
            a_digits_ptr + a_continues, b, res_digits_ptr + 1, next_carry)
    end

    # Multiplies a biguint by a single (possibly zero) digit.
    # This is the basic building block of the O(n^2) multiplication algorithm
    func mul_by_digit{range_check_ptr}(a : BigUint, b : felt) -> (res : BigUint):
        alloc_locals
        # guess a result
        local res_ptr : felt*
        # is a or b zero?  if so, return zero immediately
        if ([a.ptr] - EON) * b == 0:
            %{ ids.res_ptr = segments.gen_arg([ids.EON]) %}
            assert [res_ptr] = EON
            return (BigUint(res_ptr))
        end
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates res_ptr with correct result
            from biguint_tools import peek_one_num_from, num_mul, int_to_num
            a = peek_one_num_from(memory, ids.a.ptr)
            b = int_to_num(ids.b)
            a_mul_b = num_mul(a, b)
            ids.res_ptr = segments.gen_arg(a_mul_b)
        %}
        # Check our guess for res is a biguint (omitted because we do not expect this function to be called directly)
        # num_check(BigUint(res_ptr))
        # check res = a * b
        mul_by_nonzero_digit_helper(a.ptr, b, res_ptr, 0)
        # Return the result
        return (BigUint(res_ptr))
    end

    # Multiplies two biguint following the standard O(n^2) "long multiplication" algorithm,
    # inducting on the length of the second argument
    # mjg might be useful to hand-optimise biguint multiplication with special algorithm if both numbers consist of at most two digits.
    func mul{range_check_ptr}(a : BigUint, b : BigUint) -> (res : BigUint):
        alloc_locals
        # guess a result
        local res_ptr : felt*
        # is a or b zero, i.e. equal to [EON]?  Then return zero immediately
        if ([a.ptr] - EON) * ([b.ptr] - EON) == 0:
            %{ ids.res_ptr = segments.gen_arg([ids.EON]) %}
            assert [res_ptr] = EON
            return (BigUint(res_ptr))
        end
        # Write b as a high part `b_high`, and a final digit `b_low`.  Thus:
        #    b = b_high * PRIME + b_low
        # Then
        #    res = a * b_high * PRIME + a * b_low
        # Thus
        #    res - (a * b_low) = a * b_high * PRIME
        let b_low = [b.ptr]
        let (a__mul__b_low) = mul_by_digit(a, b_low)
        # perhaps b is a single digit, so we're done?
        if [b.ptr + 1] == EON:
            return (a__mul__b_low)
        end
        # no, b has multiple digits
        let b_high = BigUint(b.ptr + 1)
        let (a__mul__b_high) = mul(a, b_high)
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates res_ptr with correct result
            from biguint_tools import peek_one_num_from, num_mul
            a = peek_one_num_from(memory, ids.a.ptr)
            b = peek_one_num_from(memory, ids.b.ptr)
            a_mul_b = num_mul(a, b)
            ids.res_ptr = segments.gen_arg(a_mul_b)
        %}
        let res = BigUint(res_ptr)
        # Check our guess for res is a biguint
        num_check(res)
        # res - (a * b_low) = a * b_high * PRIME
        let (res___sub___a__mul__b_low, _) = sub(res, a__mul__b_low)
        # check final digit of res is equal to final digit of a * b_low
        assert [res___sub___a__mul__b_low.ptr] = 0
        # check equality of all but final digits of res - (a * b_low) and a * b_high * PRIME
        assert_eq(BigUint(res___sub___a__mul__b_low.ptr + 1), a__mul__b_high)
        # All good!  Return the result
        return (res)
    end

    # Divides biguint a by biguint b, to calculate a quotient and a remainder
    # Conforms to EVM specifications: division by 0 yields 0.
    func div{range_check_ptr}(a : BigUint, b : BigUint) -> (res : BigUint, remainder : BigUint):
        alloc_locals
        # guess a result
        local quotient_ptr : felt*
        local remainder_ptr : felt*

        # If a = 0 or b = 0, return (0, 0).
        if ([b.ptr] - EON) * ([a.ptr] - EON) == 0:
            %{
                # populate quotient and remainder with 0, 0
                ids.quotient_ptr = segments.gen_arg([ids.EON]) 
                ids.remainder_ptr = segments.gen_arg([ids.EON])
            %}
            assert [quotient_ptr] = EON
            assert [remainder_ptr] = EON
            return (BigUint(quotient_ptr), BigUint(remainder_ptr))
        end
        # OK, so a and b are nonzero.
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates quotient and remainder with correct results
            from biguint_tools import peek_one_num_from, num_div
            a = peek_one_num_from(memory, ids.a.ptr)
            b = peek_one_num_from(memory, ids.b.ptr)
            (quotient, remainder) = num_div(a, b)
            ids.quotient_ptr = segments.gen_arg(quotient)
            ids.remainder_ptr = segments.gen_arg(remainder)
        %}
        # check that nonneterministically provided quotient and remainder are valid biguints
        num_check(BigUint(quotient_ptr))
        num_check(BigUint(remainder_ptr))
        # Check that a = quotient * b + remainder
        let (quotient_mul_b) = mul(BigUint(quotient_ptr), b)
        let (quotient_mul_b__add__remainder) = add(quotient_mul_b, BigUint(remainder_ptr))
        assert_eq(a, quotient_mul_b__add__remainder)
        # Great.  Return result
        return (BigUint(quotient_ptr), BigUint(remainder_ptr))
    end

    func get_uint_one() -> (one : felt*):

        let (one_address) = get_label_location(one)
        return (one=cast(one_address, felt*))

        one:
        dw 1
        dw EON
    end

    func get_uint_two() -> (two : felt*):

        let (two_address) = get_label_location(two)
        return (two=cast(two_address, felt*))

        two:
        dw 2
        dw EON
    end

    func assert_subarray_eq{range_check_ptr}(x : felt*, y : felt*, len : felt):
        if len == 0:
            return()
        end
        assert x[0] = y[0]
        assert_subarray_eq(x = x + 1, y = y + 1, len = len - 1)
        return()
    end

    func karatsuba{range_check_ptr}(x : BigUint, y : BigUint) -> (res : BigUint):
        alloc_locals
        let (x_len) = len(x)
        let (y_len) = len(y)
        let both_single_digit = (x_len - 1) * (y_len - 1)
        # if both_single_digit == 2:
        #     tempvar arr : felt* = new (x.ptr[0] * y.ptr[0], -1)
        #     return (res = BigUint(arr))
        # end
        if both_single_digit == 0:
            #let (temp_result : BigUint) = mul(x, y)
            local temp_result : felt*
            %{
                import sys, os
                cwd = os.getcwd()
                sys.path.append(cwd)
                # hint populates quotient and remainder with correct results
                from biguint_tools import num_to_int, int_to_num, peek_one_num_from
                x = peek_one_num_from(memory, ids.x.ptr)
                x = num_to_int(x)
                y = peek_one_num_from(memory, ids.y.ptr)
                y = num_to_int(y)
                ids.temp_result = segments.gen_arg(int_to_num(x*y))
            %}
            return (res = BigUint(temp_result))
        end
        let both_zero = x_len + y_len
        if both_zero == 0:
            tempvar arr : felt* = new(-1,)
            return (res = BigUint(arr))
        end

        local n : felt
        %{
            ids.n = max(ids.x_len, ids.y_len)
        %}
        assert_nn_le(x_len, n)
        assert_nn_le(y_len, n)

        let (local m, _) = unsigned_div_rem(n, 2)

        local x_l : felt*
        local x_h : felt*

        local y_l : felt*
        local y_h : felt*
        %{
        from biguint_tools import num_to_int, int_to_num, peek_one_num_from
        x = peek_one_num_from(memory, ids.x.ptr)
        x = x[:-1]
        y = peek_one_num_from(memory, ids.y.ptr)
        y = y[:-1]
        x_l = x[:ids.m]
        x_l.append(-1)
        x_h = x[ids.m:]
        x_h.append(-1)
        y_l = y[:ids.m]
        y_l.append(-1)
        y_h = y[ids.m:]
        y_h.append(-1)
        ids.x_l = segments.gen_arg(x_l)
        ids.x_h = segments.gen_arg(x_h)
        ids.y_l = segments.gen_arg(y_l)
        ids.y_h = segments.gen_arg(y_h)
        %}
        # assert_subarray_eq(x.ptr, x_l, m)
        # assert x_l[m] = -1
        # assert_subarray_eq(x.ptr + m, x_h, m + 1)
        # assert_subarray_eq(y.ptr, y_l, m)
        # assert y_l[m] = -1
        # assert_subarray_eq(y.ptr + m, y_h, m + 1)

        let (a : BigUint) = karatsuba(x = BigUint(x_h), y = BigUint(y_h))
        let (d : BigUint) = karatsuba(x = BigUint(x_l), y = BigUint(y_l))
        
        let (b : BigUint) = add(BigUint(x_h), BigUint(x_l))
        let (c : BigUint) = add(BigUint(y_h), BigUint(y_l))

        let (e_recurse : BigUint) = karatsuba(x = b, y = c)
        let (a_d_sum : BigUint) = add(a, d)
        let (e : BigUint, _) = sub(e_recurse, a_d_sum)

        local result : felt*
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates quotient and remainder with correct results
            from biguint_tools import num_to_int, int_to_num, peek_one_num_from
            a = peek_one_num_from(memory, ids.a.ptr)
            a = num_to_int(a)

            e = peek_one_num_from(memory, ids.e.ptr)
            e = num_to_int(e)

            d = peek_one_num_from(memory, ids.d.ptr)
            d = num_to_int(d)
            x = a*(ids.SHIFT**(ids.m*2)) + e*(ids.SHIFT**ids.m) + d
            # temp = a*(SHIFT**(ids.m*2))
            # print(int_to_num(a))
            # print(int_to_num(256**(ids.m*2)))
            # print(int_to_num(temp))
            ids.result = segments.gen_arg(int_to_num(x))
        %}
        return (res = BigUint(result))
    end

    func div_karatsuba{range_check_ptr}(a : BigUint, b : BigUint) -> (res : BigUint, remainder : BigUint):
        alloc_locals
        # guess a result
        local quotient_ptr : felt*
        local remainder_ptr : felt*

        # If a = 0 or b = 0, return (0, 0).
        if ([b.ptr] - EON) * ([a.ptr] - EON) == 0:
            %{
                # populate quotient and remainder with 0, 0
                ids.quotient_ptr = segments.gen_arg([ids.EON]) 
                ids.remainder_ptr = segments.gen_arg([ids.EON])
            %}
            assert [quotient_ptr] = EON
            assert [remainder_ptr] = EON
            return (BigUint(quotient_ptr), BigUint(remainder_ptr))
        end
        # OK, so a and b are nonzero.
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates quotient and remainder with correct results
            from biguint_tools import peek_one_num_from, num_div
            a = peek_one_num_from(memory, ids.a.ptr)
            b = peek_one_num_from(memory, ids.b.ptr)
            (quotient, remainder) = num_div(a, b)
            ids.quotient_ptr = segments.gen_arg(quotient)
            ids.remainder_ptr = segments.gen_arg(remainder)
        %}
        # check that nonneterministically provided quotient and remainder are valid biguints
        num_check(BigUint(quotient_ptr))
        num_check(BigUint(remainder_ptr))
        let (rem_is_not_zero) = is_not_zero(BigUint(remainder_ptr))
        # Check that a = quotient * b + remainder
        let (quotient_mul_b : BigUint) = karatsuba(BigUint(quotient_ptr), b)
        let (quotient_mul_b__add__remainder) = add(quotient_mul_b, BigUint(remainder_ptr))
        assert_eq(a, quotient_mul_b__add__remainder)
        # Great.  Return result
        return (BigUint(quotient_ptr), BigUint(remainder_ptr))
    end

    func mul_mod{range_check_ptr}(a : BigUint, b: BigUint, m : BigUint) -> (res : BigUint):
        alloc_locals
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            # hint populates quotient and remainder with correct results
            from biguint_tools import peek_one_num_from, num_div
            a = peek_one_num_from(memory, ids.a.ptr)
            b = peek_one_num_from(memory, ids.b.ptr)
            m = peek_one_num_from(memory, ids.m.ptr)
            print(len(a), len(b), len(m))
        %}
        if a.ptr[0] == -1:
            return (res = a)
        end
        if b.ptr[0] == -1:
            return (res = b)
        end

        let a_is_one = a.ptr[0] * a.ptr[1]
        if a_is_one == -1:
            return (res = b)
        end
        
        let b_is_one = b.ptr[0] * b.ptr[1]
        if b_is_one == -1:
            return (res = a)
        end

        let (two) = get_uint_two()
        let (q, r) = div(b, BigUint(two))
        let (a_2 : BigUint) = mul_mod(a, q, m)

        let (r_is_not_zero) = is_not_zero(r)

        local res : felt*
        if r_is_not_zero == 0:
            let (sum) = add(a_2, a_2)
            let (_, sum_mod) = div(sum, m)
            res = sum_mod.ptr
        else:
            let (_, a_mod) = div(a, m)
            let (sum) = add(a_2, a_2)
            let (final_sum) = add(sum, a_mod)
            let (_, result) = div(final_sum, m)
            res = result.ptr
        end
        return (res = BigUint(res))
    end

    func mul_mod_with_hints{range_check_ptr}(a : BigUint, b : BigUint, m : BigUint) -> (res : BigUint):
        alloc_locals
        local q : felt*
        local rem : felt*
        local hint_product : felt*
        %{
            import sys, os
            cwd = os.getcwd()
            sys.path.append(cwd)
            from biguint_tools import num_to_int, int_to_num, peek_one_num_from
            a = num_to_int(peek_one_num_from(memory, ids.a.ptr))
            b = num_to_int(peek_one_num_from(memory, ids.b.ptr))
            m = num_to_int(peek_one_num_from(memory, ids.m.ptr))
            y = (a * b) % m
            # print(y, (a * b // m) + m)
            # print()
            result = int_to_num(y)
            ids.rem = segments.gen_arg(result)
            ids.q = segments.gen_arg(int_to_num((a * b) // m))
            ids.hint_product = segments.gen_arg(int_to_num(a * b))
        %}
        let (product : BigUint) = mul(a, b)
        let (quotient : BigUint, remainder : BigUint) = div(product, m)
        # let (sum : BigUint) = add(quotient, BigUint(rem))
        assert_eq(BigUint(rem), remainder)

        return (res = BigUint(rem))
    end

    func pow_mod_felt_exponent{range_check_ptr}(s : BigUint, e : felt, m : BigUint) -> (res : BigUint):
        alloc_locals
        if s.ptr[0] == EON:
            let (one) = get_uint_one()
            return (res = BigUint(one))
        end
        
       
        if e == 1:
            # let (_, base) = div(s, m)
            return (res = s)
        end

        let (q, r) = unsigned_div_rem(e, 2)

        tempvar range_check_ptr = range_check_ptr
        local res : felt*
        if r == 0:
            # let (square : BigUint) = mul(s, s)
            # let (_, squareRem) = div(square, m)
            # let (squareRem) = mul_mod(s, s, m)
            let (squareRem) = mul_mod_with_hints(s, s, m)
            let (result : BigUint) = pow_mod_felt_exponent(s = squareRem, e = q, m = m)
            res = result.ptr
            tempvar range_check_ptr = range_check_ptr
        else:
            let new_e = e - 1
            let (recurse : BigUint) = pow_mod_felt_exponent(s = s, e = new_e, m=m)
            # let (product : BigUint) = mul(s, recurse)
            # let (_, result) = div(product, m)
            # let (result) = mul_mod(s, recurse, m)
            let (result) = mul_mod_with_hints(s, recurse, m)
            res = result.ptr
            tempvar range_check_ptr = range_check_ptr
        end

        return (res = BigUint(res))

    end

    func pow_mod{range_check_ptr}(s : BigUint, e: BigUint, m : BigUint) -> (res : BigUint):
        alloc_locals
        if s.ptr[0] == EON:
            let (one) = get_uint_one()
            return (res = BigUint(one))
        end

        let (result : BigUint) = _pow_mod_inner(s = s, e = e, m = m)
        return (res = result)
    end

    func _pow_mod_inner{range_check_ptr}(s : BigUint, e: BigUint, m : BigUint) -> (res : BigUint):
        alloc_locals

        let (local one) = get_uint_one()

        let (local two) = get_uint_two()

        let (_, local base) = div(s, m)

        let (e_is_one : felt) = is_eq(e, BigUint(one))
        if e_is_one == 1:
            return (res = base)
        end

        let (q : BigUint, rem : BigUint) = div(e, BigUint(two))
        let (E_is_odd : felt) = is_not_zero(rem)

        if E_is_odd == 0:
            let (square : BigUint) = mul(base, base)
            let (_, local squareRem) = div(square, m)
            let (result : BigUint) = _pow_mod_inner(s = squareRem, e = q, m = m)
            return (res = result)
        end
        
        if E_is_odd == 1:
            let (even_exponent, _) = sub(e, BigUint(one))
            let (recurse : BigUint) = _pow_mod_inner(s = base, e = even_exponent, m=m)
            let (product : BigUint) = mul(base, recurse)
            let (_, result) = div(product, m)
            return (res = result)
        end

        return (res = BigUint(one))
    end

end
# end namespace

# The code below should not be executed.  Its role is to reference the functions in the namespace above, to prevent the Cairo code optimiser from garbage-collecting the namespace's contents as dead code.
# One might call the code below a "dead code dead code eliminator eliminator", if one were inclined to dry wit.
func dead_code_dead_code_eliminator_eliminator_for_biguint_namespace{range_check_ptr}():
    alloc_locals
    local a : felt*
    local b : felt*
    let num_a = biguint.BigUint(a)
    let num_b = biguint.BigUint(b)
    biguint.num_check{range_check_ptr=range_check_ptr}(num_a)
    biguint.id(num_a)
    biguint.len(num_a)
    biguint.is_not_zero(num_a)
    biguint.is_eq(num_a, num_b)
    biguint.assert_eq(num_a, num_b)
    biguint.compare(num_a, num_b)
    biguint.is_lt(num_a, num_b)
    biguint.is_le(num_a, num_b)
    biguint.add(num_a, num_b)
    biguint.sub(num_a, num_b)
    biguint.mul(num_a, num_b)
    biguint.div(num_a, num_b)
    return ()
end