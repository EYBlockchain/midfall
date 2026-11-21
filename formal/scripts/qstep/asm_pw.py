import sys, re
exec(open('/private/tmp/pw_parts.py').read())
exec(open('/private/tmp/pw_parts2.py').read())
T = open('/private/tmp/pw_template.txt').read()
T = re.sub(r'\\u([0-9a-fA-F]{4})', lambda m: chr(int(m.group(1),16)), T)
for _pass in range(3):
    for k, v in PARTS.items():
        T = T.replace('@@' + k + '@@', v)
left = sorted(set(re.findall(r'@@[A-Za-z0-9_]+@@', T)))
assert not left, left
open('/private/tmp/pw_lean.txt','w').write(T)
print('pw chars', len(T))
