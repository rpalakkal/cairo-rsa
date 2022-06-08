%builtins range_check
from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.registers import get_label_location
from sha256.sha256 import finalize_sha256, sha256
from int_unbounded.biguint import biguint

func main{range_check_ptr}():
    alloc_locals

    let (local sha256Prefix) = getSha256Prefix()
    
    let sha256PrefixLength = 19

    local em : felt*
    local em_real_check : felt*
    local em_size : felt

    local s : felt*
    local e : felt*
    local m : felt*
    local exponent : felt

    local test : felt*
    local test2 : felt*
    %{
        import sys, os
        cwd = os.getcwd()
        sys.path.append(cwd)
        from biguint_tools import int_to_num
        m = int(program_input['modulus'], 16)
        e = int(program_input['exponent'], 16)
        s = int(program_input['signature'], 16)
        ids.exponent = e
        res = pow(s, e, m)
        ids.em_real_check = segments.gen_arg(int_to_num(res))
        res = res.to_bytes((m.bit_length() + 7) // 8, byteorder = 'big')
        ids.em = segments.gen_arg(res)
        ids.em_size = len(res)
        s_array = int_to_num(s)
        e_array = int_to_num(e)
        m_array = int_to_num(m)
        ids.s = segments.gen_arg(s_array)
        ids.e = segments.gen_arg(e_array)
        ids.m = segments.gen_arg(m_array)
    %}
    #let (em_real : biguint.BigUint) = biguint.pow_mod(biguint.BigUint(s), biguint.BigUint(e), biguint.BigUint(m))
    let (em_real : biguint.BigUint) = biguint.pow_mod_felt_exponent(biguint.BigUint(s), exponent, biguint.BigUint(m))
    #let (em_real : biguint.BigUint) = biguint.mul_mod(a = biguint.BigUint(s), b = biguint.BigUint(s), m = biguint.BigUint(m))
    %{
        import sys, os
        cwd = os.getcwd()
        sys.path.append(cwd)
        # hint populates quotient and remainder with correct results
        from biguint_tools import num_to_int, int_to_num, peek_one_num_from
        a = peek_one_num_from(memory, ids.em_real.ptr)
        a = num_to_int(a)
        s = int(program_input['signature'], 16)
    %}

    biguint.assert_eq(em_real, biguint.BigUint(em_real_check))


    assert [em] = 0x00
    assert [em+1] = 0x01

    # check padding
    let paddingLen = em_size - sha256PrefixLength - 3 - 32
    checkPadding(arr = em+2, size = paddingLen)

    # check sha256 prefix
    assert [em + 2 + paddingLen] = 0x00
    checkSha256Prefix(arr = em + paddingLen + 3, prefix = sha256Prefix, size = sha256PrefixLength)

    return ()
end

func checkPadding(arr: felt*, size: felt):
    if size == 0:
        return ()
    end

    assert [arr] = 0xff
    checkPadding(arr = arr + 1, size = size-1)
    return ()
end

func checkSha256Prefix(arr: felt*, prefix: felt*, size: felt):
    if size == 0:
        return ()
    end 
    assert [arr] = [prefix]
    checkSha256Prefix(arr = arr + 1, prefix = prefix + 1, size = size - 1)
    return ()
end

func getSha256Prefix() -> (prefix : felt*):

    let (prefix_address) = get_label_location(prefix_start)
    return (prefix=cast(prefix_address, felt*))

    prefix_start:
    dw 0x30
    dw 0x31
    dw 0x30
    dw 0x0d
    dw 0x06
    dw 0x09
    dw 0x60
    dw 0x86
    dw 0x48
    dw 0x01
    dw 0x65
    dw 0x03
    dw 0x04
    dw 0x02
    dw 0x01
    dw 0x05
    dw 0x00
    dw 0x04
    dw 0x20
end