p = 21448884629509455597215930748900681159323242237303782800136123960324312583790994045488533691889446581945518026508097
q = 39128794508258790515072383975390806261898062361839764511933549761670978999997096053314214965077731424736773956742363
n = p*q
print("p bits", p.nbits(), "q bits", q.nbits())
print("p-q bits", (p-q).nbits(), "p+q bits", (p+q).nbits())
print("ratio p/q ~", float(p)/float(q))
print()
for name, v in [("p-1",p-1),("q-1",q-1),("p+1",p+1),("q+1",q+1)]:
    f = factor(v, limit=10^6, proof=False)
    rem = v
    for prime,e in f:
        rem //= prime^e
    print(name, "small factors:", f)
    print("   remaining cofactor bits:", rem.nbits(), "prime?", is_pseudoprime(rem))
print()
print("gcd(p-1,q-1) =", gcd(p-1,q-1))
print("gcd(p-1,q+1) =", gcd(p-1,q+1))
print("gcd(p+1,q-1) =", gcd(p+1,q-1))
print("gcd(p+1,q+1) =", gcd(p+1,q+1))
