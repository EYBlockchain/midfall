import qparse, re
src = open(qparse.GENFILE).read()
i = src.find("def qArmBodyAddMemU16")
j = src.find("\n\n", i)
body = src[src.find(":=", i)+2:j]
print(repr(body[:160]))
print(qparse.tokenize(body)[:20])
