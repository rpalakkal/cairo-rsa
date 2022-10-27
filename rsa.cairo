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
    let (num_limbs_rounded, first_limb_len) = unsigned_div_rem(key_size, bitLength)
    let num_limbs = num_limbs_rounded + 1

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
    let (first_limb) = computeFirstLimbBase120(em = em, e = first_limb_len - 8)
    assert em_real.ptr[num_limbs-1] = first_limb
    checkBase120Result(base120 = em_real.ptr + num_limbs - 2, arr = em+8, size = num_limbs-1)

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

func computeFirstLimbBase120(em: felt*, e: felt) -> (value: felt):
    alloc_locals
    if e == 0:
        return (value = [em])
    end
    let (powers: felt*) = getPowersOf2()
    let currTerm = [em] * powers[e]
    let (recurse) = computeFirstLimbBase120(em = em + 1, e = e - 8)
    return (value = currTerm + recurse)
end

func checkBase120Result(base120: felt*, arr: felt*, size: felt):
    alloc_locals
    local w = [arr] * (2**112) + [arr+1] * (2**104) + [arr+2] * (2**96) + [arr+3] * (2**88) + [arr+4] * (2**80) + [arr+5] * (2**72) + [arr+6] * (2**64) + [arr+7] * (2**56) + [arr+8] * (2**48) + [arr+9] * (2**40) + [arr+10] * (2**32) + [arr+11] * (2**24) + [arr+12] * (2**16) + [arr+13] * (2**8) + [arr+14]
    assert [base120] = w
    if size - 1 == 0:
        return ()
    end
    checkBase120Result(base120 = base120 - 1, arr = arr+15, size = size-1)
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

func getPowersOf2() -> (prefix : felt*):

    let (prefix_address) = get_label_location(powers_of_two)
    return (prefix=cast(prefix_address, felt*))

    powers_of_two:
    dw 2**0
    dw 2**1
    dw 2**2
    dw 2**3
    dw 2**4
    dw 2**5
    dw 2**6
    dw 2**7
    dw 2**8
    dw 2**9
    dw 2**10
    dw 2**11
    dw 2**12
    dw 2**13
    dw 2**14
    dw 2**15
    dw 2**16
    dw 2**17
    dw 2**18
    dw 2**19
    dw 2**20
    dw 2**21
    dw 2**22
    dw 2**23
    dw 2**24
    dw 2**25
    dw 2**26
    dw 2**27
    dw 2**28
    dw 2**29
    dw 2**30
    dw 2**31
    dw 2**32
    dw 2**33
    dw 2**34
    dw 2**35
    dw 2**36
    dw 2**37
    dw 2**38
    dw 2**39
    dw 2**40
    dw 2**41
    dw 2**42
    dw 2**43
    dw 2**44
    dw 2**45
    dw 2**46
    dw 2**47
    dw 2**48
    dw 2**49
    dw 2**50
    dw 2**51
    dw 2**52
    dw 2**53
    dw 2**54
    dw 2**55
    dw 2**56
    dw 2**57
    dw 2**58
    dw 2**59
    dw 2**60
    dw 2**61
    dw 2**62
    dw 2**63
    dw 2**64
    dw 2**65
    dw 2**66
    dw 2**67
    dw 2**68
    dw 2**69
    dw 2**70
    dw 2**71
    dw 2**72
    dw 2**73
    dw 2**74
    dw 2**75
    dw 2**76
    dw 2**77
    dw 2**78
    dw 2**79
    dw 2**80
    dw 2**81
    dw 2**82
    dw 2**83
    dw 2**84
    dw 2**85
    dw 2**86
    dw 2**87
    dw 2**88
    dw 2**89
    dw 2**90
    dw 2**91
    dw 2**92
    dw 2**93
    dw 2**94
    dw 2**95
    dw 2**96
    dw 2**97
    dw 2**98
    dw 2**99
    dw 2**100
    dw 2**101
    dw 2**102
    dw 2**103
    dw 2**104
    dw 2**105
    dw 2**106
    dw 2**107
    dw 2**108
    dw 2**109
    dw 2**110
    dw 2**111
    dw 2**112
end