l = open('/tmp/qtest1.lean').read().split(chr(10))[47]
print(repr(l[:60]))
for i,ch in enumerate(l[:40]):
    print(i+1, repr(ch))
