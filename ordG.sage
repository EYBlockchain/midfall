p = 21448884629509455597215930748900681159323242237303782800136123960324312583790994045488533691889446581945518026508097
q = 39128794508258790515072383975390806261898062361839764511933549761670978999997096053314214965077731424736773956742363
A = 0x1115160ded643518fc0b46ad430da8e5c15f85fe03d0b6b181060f8c167714c650b31b4850b2f06430903acabcee293a8f88eb2a94554636fe823e6b6e753f7de3b6436b32518715df94030bf910993d5158cf47c83042e3fff16181819155f4
G = (0x858cd5e8856db40d611f0c8a605296b64146118a5112bd5f25333eecbcb0b22ba689491990304ac0c709e99af8cc0c789131f940ec79936f4c75a24ef7165eb1e53f0ffb46a931d2ec95ba678b5825cb3649ab4d4e4b206dcbc62236fefa3bc1,0x461e32608d4000477828abe7e900882d9864d3792b38a332b6fab213a9bf840fe3cb7b3be185266143c493e8d10d9cf37ea8f90695b7e6bdc17938cb7d11dd4e40f7f4037e9e0e3307e4e1de207f56a51e62eab3bb21ca6ebbc3f9bc8e4be604)
n=p*q
B=(G[1]^2-G[0]^3-A*G[0])%n

for name, pr in [("p",p),("q",q)]:
    E = EllipticCurve(GF(pr), [A % pr, B % pr])
    P = E(G)
    N = E.order()
    print(name, "N bits", N.nbits(), "N =", N)
    if is_prime(N):
        print(name, "N is prime; ord(G) =", N)
        continue
    f = factor(N)
    print(name, "N factorization:", f)
    # compute exact order of P
    o = N
    for prime,e in f:
        for _ in range(e):
            if (o//prime)*P == E(0):
                o //= prime
            else:
                break
    print(name, "ord(G) =", o)
    print(name, "ord(G) factorization:", factor(o))
