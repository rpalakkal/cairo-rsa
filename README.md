# cairo-rsa

RSA verification according to the RSA Sha256 Pkcs1.5 signature standard in Cairo.

## About
This library makes use of the `biguint` Cairo library ([GitHub](https://github.com/bellissimogiorno/cairo-integer-types/tree/main/int_unbounded)), which allows for integers of arbitrary size. With felts having a max size of 251 bits, the `biguint` library supports storing numbers up to base 125. We use base 120 as it is the largest multiple of 8 supported (and this allows us to more easily compare chunks of 8 bit words with the 120 bit limbs). We use the`biguint` library to store an unbounded unsigned integer in base 120 as a list of felts with least significant digits first and terminated with EON (-1). 

Note: to convert an integer into its `biguint` base 120 representation, use the `num_to_int` function from [biguint_tools.py](https://github.com/rpalakkal/cairo-rsa/blob/main/biguint_tools.py).

## Usage
```
func rsaVerify{range_check_ptr, bitwise_ptr : BitwiseBuiltin*}(n: felt*, s: felt*, message: felt*, message_len: felt, e: felt, key_size: felt)
```
Parameters:

* `n` -- RSA modulus as a `felt*` for a `biguint` in base 120
* `s` -- RSA signature to be verified as a `felt*` for a `biguint` in base 120
* `message` -- the signed message, split into (up to) 14 words of 32 bits (big endian)
* `message_len` -- the byte length of the message
* `e` -- RSA exponent as a `felt`
* `key_size` -- the size of the modulus and signature in bits

For example (with n, s, and e stored in `input.json`):
```
let (local hello_world) = alloc()
assert hello_world[0] = 'hell'
assert hello_world[1] = 'o wo'
assert hello_world[2] = 'rld\x00' # Note the '\x00' padding.

%{
	import sys, os
	cwd = os.getcwd()
	sys.path.append(cwd)
	from biguint_tools import int_to_num
	n =  int(program_input['modulus'], 16)
	e =  int(program_input['exponent'], 16)
	s =  int(program_input['signature'], 16)
	ids.e = e
	ids.s = segments.gen_arg(int_to_num(s))
	ids.n = segments.gen_arg(int_to_num(n))
}%

rsaVerify(n = n, s = s, message = hello_world, message_len = 11, e = e, key_size = 1024)
```

## Testing

As the `biguint` library is in Cairo 0.8, this library is also in Cairo 0.8 for now. 

To compile the test, run:
```
cairo-compile rsaTest.cairo --output rsa_compiled.json
```

To execute the test, run:
```
cairo-run --program=rsa_compiled.json --print_output  --program_input=input.json --print_info --layout=all 
```