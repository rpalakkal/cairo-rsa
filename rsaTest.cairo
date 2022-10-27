%builtins range_check bitwise
from rsa import rsaVerify
from starkware.cairo.common.cairo_builtins import BitwiseBuiltin
from starkware.cairo.common.registers import get_label_location
from starkware.cairo.common.alloc import alloc

func main{range_check_ptr, bitwise_ptr : BitwiseBuiltin*}():

    # let (s, n, e, message, message_len, key_size) = getHelloWorldInputs()
    let (s, n, e, message, message_len, key_size) = getInputFromJSON()
    rsaVerify(n = n, s = s, message = message, message_len = message_len, e = e, key_size = key_size)

    return ()
end

func getHelloWorldInputs() -> (s: felt*, n: felt*, e: felt, message: felt*, message_len: felt, key_size: felt):
    alloc_locals
    let (local s) = getSConstant()
    let (local n) = getMConstant()

    let e = 65537

    let (local hello_world) = alloc()
    assert hello_world[0] = 'hell'
    assert hello_world[1] = 'o wo'
    assert hello_world[2] = 'rld\x00'

    return (s = s, n=n, e=e, message = hello_world, message_len = 11, key_size = 1024)
end

func getInputFromJSON() -> (s: felt*, n: felt*, e: felt, message: felt*, message_len: felt, key_size: felt):
    alloc_locals

    local s : felt*
    local n : felt*
    local e : felt

    local message : felt*
    local message_len: felt
    local key_size: felt

    %{
        import sys, os
        cwd = os.getcwd()
        sys.path.append(cwd)
        from biguint_tools import int_to_num
        n = int(program_input['modulus'], 16)
        e = int(program_input['exponent'], 16)
        s = int(program_input['signature'], 16)
        ids.e = e
        ids.s = segments.gen_arg(int_to_num(s))
        ids.n = segments.gen_arg(int_to_num(n))

        byte_string = str.encode(program_input['message'])
        byte_string_len = len(byte_string)
        bytes_to_add = 4 - byte_string_len%4 
        arr = list(byte_string) + [0x00] * bytes_to_add
        input_arr = []
        for i in range(int(len(arr)/4)):
            start = 4*i
            end = 4*i + 4
            word = arr[start:end]
            input_arr.append(int.from_bytes(word, "big"))
        ids.message = segments.gen_arg(input_arr)
        ids.message_len = byte_string_len
        ids.key_size = program_input['keySize']
    %}
    return (s = s, n = n, e = e, message = message, message_len = message_len, key_size = key_size)
end

func getSConstant() -> (data: felt*):
    let (data_address) = get_label_location(s_start)
    return (data=cast(data_address, felt*))

    s_start:
    dw 784307230782663912082048397506985010
    dw 765851227150313327115085968184970341
    dw 160340605318157471334399115666052392
    dw 585118888975899709966952992146357044
    dw 673587493630549148696759681954032544
    dw 416043659050947764264452888069296302
    dw 1106777874743560891481989886465950190
    dw 454878250843762721249528638230965671
    dw 6314282666792471965
    dw -1
end

func getMConstant() -> (data: felt*):
    let (data_address) = get_label_location(m_start)
    return (data=cast(data_address, felt*))

    m_start:
    dw 866498406123682060196155202048282615
    dw 854158375808763579005844814675697716
    dw 1177606932465822714070091980452590696
    dw 532700527583281371741714420375138095
    dw 1139373369115769442136792100485827312
    dw 990592174206139566147341456451864229
    dw 412010817050331869404184376112667927
    dw 615602434747306972905599224787730457
    dw 13228183682417102765
    dw -1
end