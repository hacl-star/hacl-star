# If it's a tuple, first element is used for the variable name,
# second element for the content. If it is a single string, it
# is used for both name and content.
#
# Variable name will be prefixed with "label_" (see template variable)

labels = [
    ("rfcXXXX", "RFCXXXX "),
    "dh",
    "prk",
    "pskID_hash",
    "info_hash",
    "psk_hash",
    "secret",
    "key",
    "nonce",
    "exp",
    "sec"
]

template = """// generated: "{label_content}"
inline_for_extraction
let size_label_{label_name}: size_nat = {label_size}
let label_{label_name}_list : l:list uint8{{List.Tot.length l == size_label_{label_name}}} =
  [@inline_let]
  let l = [{byte_list}] in
  assert_norm(List.Tot.length l == size_label_{label_name});
  l
let label_{label_name} : lbytes size_label_{label_name} = createL label_{label_name}_list
"""

byte_template = "u8 {byte};"

def string_to_byte_list(str):
    byte_list = ""
    for c in str:
        byte = hex(ord(c))
        byte_list += byte_template.format(**locals()) + " "
    return byte_list[:-2] # remove last space and ;

for label in labels:
    if type(label) == tuple:
        label_name = label[0]
        label_content = label[1]
    else:
        label_name = label
        label_content = label
    label_size = len(label_content)
    byte_list = string_to_byte_list(label_content)
    print(template.format(**locals()))
    print()
