from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.math import unsigned_div_rem
from starkware.cairo.common.registers import get_label_location
from starkware.cairo.common.cairo_builtins import BitwiseBuiltin
from sha256.sha256 import finalize_sha256, sha256
from int_unbounded.biguint import biguint

const sha256PrefixLength = 19
const bitLength = 120

func rsaVerify{range_check_ptr, bitwise_ptr : BitwiseBuiltin*}(n: felt*, s: felt*, message: felt*, message_len: felt, e: felt, key_size: felt):
    alloc_locals

    let (local sha256Prefix) = getSha256Prefix()
    let em_size = key_size / 8

    local em : felt*
    %{
        import sys, os
        cwd = os.getcwd()
        sys.path.append(cwd)
        from biguint_tools import peek_one_num_from, num_to_int
        n = num_to_int(peek_one_num_from(memory, ids.n))
        s = num_to_int(peek_one_num_from(memory, ids.s))
        res = pow(s, ids.e, n)
        res = res.to_bytes((n.bit_length() + 7) // 8, byteorder = 'big')
        ids.em = segments.gen_arg(res)
    %}

    let (em_real : biguint.BigUint) = biguint.pow_mod_felt_exponent(biguint.BigUint(s), e, biguint.BigUint(n))

    # make sure that em (populated from hint) has the same value as em_real
    let (local reversed_em: felt*) = alloc()
    assert reversed_em[0] = em_real.ptr[8]
    assert reversed_em[1] = em_real.ptr[7]
    assert reversed_em[2] = em_real.ptr[6]
    assert reversed_em[3] = em_real.ptr[5]
    assert reversed_em[4] = em_real.ptr[4]
    assert reversed_em[5] = em_real.ptr[3]
    assert reversed_em[6] = em_real.ptr[2]
    assert reversed_em[7] = em_real.ptr[1]
    assert reversed_em[8] = em_real.ptr[0]
    local first_limb = [em] * (2**56) + [em+1] * (2**48) + [em+2] * (2**40) + [em+3] * (2**32) + [em+4] * (2**24) + [em+5] * (2**16) + [em+6] * (2**8) + [em+7]
    assert reversed_em[0] = first_limb
    checkBase120Result(base120 = reversed_em + 1, arr = em+8, size = 8)

    #check leading bits
    assert [em] = 0x00
    assert [em+1] = 0x01

    # check padding
    let paddingLen = em_size - sha256PrefixLength - 3 - 32
    checkPadding(arr = em+2, size = paddingLen)

    # check sha256 prefix
    assert [em + 2 + paddingLen] = 0x00
    checkSha256Prefix(arr = em + paddingLen + 3, prefix = sha256Prefix, size = sha256PrefixLength)

    #check sha256
    let (local sha256_ptr_start : felt*) = alloc()
    let sha256_ptr = sha256_ptr_start
    let (hash) = sha256{sha256_ptr=sha256_ptr}(message, message_len)
    finalize_sha256(sha256_ptr_start=sha256_ptr_start, sha256_ptr_end=sha256_ptr)

    checkSha256(arr = em+3+paddingLen+sha256PrefixLength, hash = hash, size = 8)
    return ()
end

func checkBase120Result(base120: felt*, arr: felt*, size: felt):
    alloc_locals
    if size == 0:
        return ()
    end
    local w = [arr] * (2**112) + [arr+1] * (2**104) + [arr+2] * (2**96) + [arr+3] * (2**88) + [arr+4] * (2**80) + [arr+5] * (2**72) + [arr+6] * (2**64) + [arr+7] * (2**56) + [arr+8] * (2**48) + [arr+9] * (2**40) + [arr+10] * (2**32) + [arr+11] * (2**24) + [arr+12] * (2**16) + [arr+13] * (2**8) + [arr+14]
    assert [base120] = w
    checkBase120Result(base120 = base120 + 1, arr = arr+15, size = size-1)
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

func checkSha256(arr: felt*, hash: felt*, size: felt):
    alloc_locals
    if size == 0:
        return ()
    end
    local w0 = [arr] * (2**24) + [arr+1] * (2**16) + [arr+2] * (2**8) + [arr+3]
    assert [hash] = w0
    checkSha256(arr = arr+4, hash = hash + 1, size = size-1)
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