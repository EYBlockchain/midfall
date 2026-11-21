import sys
exec(open('/private/tmp/row_parts.py').read())
T = open('/private/tmp/row_template.txt').read()
import re
T = re.sub(r'\\u([0-9a-fA-F]{4})', lambda m: chr(int(m.group(1),16)), T)
for _pass in range(3):
    for k, v in PARTS.items():
        T = T.replace('@@' + k + '@@', v)
assert '@@' not in T, [x for x in T.split() if x.startswith('@@')][:3]
open('/private/tmp/row_lean.txt','w').write(T)
print('row chars', len(T))