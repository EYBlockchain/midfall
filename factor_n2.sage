n = 839268999099425968807411462926249098389252581409067470253664485759322114291073830711064449642314699377238366107656217249459455592803416447657121161867800269745726650461218600418110039592265036637486587632551853112632091434362413211
# Fermat closeness test
a = isqrt(n)
if a*a < n: a += 1
b2 = a*a - n
print("Fermat initial b2 is square?", b2.is_square())
# check a few thousand
for i in range(20000):
    if b2.is_square():
        print("Fermat FOUND", a-isqrt(b2), a+isqrt(b2)); break
    a += 1; b2 = a*a - n
else:
    print("Fermat no luck in 20000 steps")

print("p-1 10^6:", factor(n, limit=10^6, proof=False))
