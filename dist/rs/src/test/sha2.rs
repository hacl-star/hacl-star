#![allow(non_upper_case_globals)]
#![allow(dead_code)]

#[test]
pub fn test_sha2() {
    let state = crate::hacl::hash_sha2::malloc_256();
    let state_ref = &mut*state.into_boxed_slice();
    // Meh. Copy.
    let input = b"BsPzn7jdiXtsl/u/InjqfivA0iPjoMFTD6QcLkZUh0dYchilWrlinINHfSZL+5or5NtNGL1aJDHfckYuWKEsMrm+8ebESvApqA+dJHSna5RYtSMbB8r8gii/nmC9hxmw85RHCtDeQTE9NQdsl+kKg21741E2bjU4MX6Glos6SEIoRfHKWEXbHz9qcdl6aD46LnhtBuhvyNIa4XRL0yTiM0o1PLQUX6sB8WMXUFCtqSy6WYRiIvtR8qFfr+5mBpGSCX7t8ihmvLn5eeme3K+1NAQAkhc/IISkqH57AmEi/vapQ/Jyi0KnPSwlb8Gs/iPK9yn/qSJsdnhHKH+8BPraP7Nw4OAlDyfbhNjG0HbTnnfwDF4m+fLhfnACSTPEN5QHpWr+/ECF9ivhalEAR0GeeZLYJ3o8UYhh8IxzpeHjD6Mi4LB39g3AUz1DDAfdfUBUmNK8rUOzEUE31gXcUY5/elg3LUfyKg8FRU0IAo3fDhcegFQpzDmLYoDEORlVLIaXe349ERRsrPpMKZ49DMK4mt4i+bbNC93gfkbCiufOo+sc1EANY4kISzVD6vvk89zGKxVLpl7dwJQZydsr8jGb8I78cLbRDHQSFlpwdUEm7bqrB7y2al8kExE/N/dh+FX+upf7nF+9TCYfW3lqAbrjMU6xstOLZB5UlMk2ZVf3tAPOkG/I1X+eUDeBrdAtpcbErXGGSkQo3WMxBB8afRbfqUDzH8AVmtdxIrzpMgaBqwGidaVqLIircfKsRUl+2XZX+EAzx4FJS4tMFQ5Jsx+fUenN/o8jD/3iH0JVH+M8XcmMeJYacPDvt283Pe6BpKp1Fshq+AsUoAjWdlj1x9m6LUYlsFnxQnlGNpH4iGmbdi44nreYdO+4xVNFV14nD583Yt+lrzBRmFQ3/TGPqlESdraPwiT1aU8f4isLv13E3xY8g96GDBuI71hhbVAHIgamKtkb9X9eQnUZ8zFSW05jdcTykG4iMEE2QA/NHlQy1H1jzsm8wquhGSzHOwWfBAMWwM0rkNz0l7jelGJpZcvlukmENIGya7yfCtMww6fYZFQ9InTlAQ2G3V2NxqIf7bVBm7wJG8YFz5JggFN3Bh6H37AvOgb59KeRGtsKmLCffA00zzJROE357kiKnyVMB9fem3cvKT2QFmGYC3F8lQ+x8GfaEA3uxaGUyvenf2ujvZsl/D15MEllX1BE7xUYo9+IbPXkr37VYj9GlMSavjiLW8KXzJdNXBPpSTNEllrLxFCw715c9lG5d+fIlApcxQ/Fp+JKf3eNNnDDKIKh7d90QH2T6/cY0CiOY15dwYaDVQX7f+A4trFPXFLKYm+0jr9xP3NrjKEslxC/NTQACQCQ+g==\n";
    let mut input_ = *input;
    crate::hacl::hash_sha2::update_256(state_ref, &mut input_, input.len() as u32);
    let mut output = [0u8; 32];
    crate::hacl::hash_sha2::digest_256(state_ref, &mut output);
    let expected = [ 0xad, 0xfd, 0xbc, 0x34, 0x8b, 0x94, 0x26, 0x7e, 0x97, 0x16, 0x02, 0xe3, 0x46, 0x4d, 0xd9, 0xdb, 0xaf, 0x94, 0x51, 0x52, 0xbf, 0xdb, 0x2d, 0xfb, 0xcd, 0x66, 0xb7, 0x3c, 0x51, 0x20, 0x03, 0xbb ];
    assert_eq!(output, expected);
}
