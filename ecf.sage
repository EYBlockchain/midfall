import sys, time
A = 0x1115160ded643518fc0b46ad430da8e5c15f85fe03d0b6b181060f8c167714c650b31b4850b2f06430903acabcee293a8f88eb2a94554636fe823e6b6e753f7de3b6436b32518715df94030bf910993d5158cf47c83042e3fff16181819155f4
n = 839268999099425968807411462926249098389252581409067470253664485759322114291073830711064449642314699377238366107656217249459455592803416447657121161867800269745726650461218600418110039592265036637486587632551853112632091434362413211
G = (0x858cd5e8856db40d611f0c8a605296b64146118a5112bd5f25333eecbcb0b22ba689491990304ac0c709e99af8cc0c789131f940ec79936f4c75a24ef7165eb1e53f0ffb46a931d2ec95ba678b5825cb3649ab4d4e4b206dcbc62236fefa3bc1,0x461e32608d4000477828abe7e900882d9864d3792b38a332b6fab213a9bf840fe3cb7b3be185266143c493e8d10d9cf37ea8f90695b7e6bdc17938cb7d11dd4e40f7f4037e9e0e3307e4e1de207f56a51e62eab3bb21ca6ebbc3f9bc8e4be604)
O = (0,0)

def add_chk(P, Q):
    # returns (R, g). g>1 means found a factor (gcd of denominator with n)
    if P == O: return Q, 1
    if Q == O: return P, 1
    x1,y1 = P; x2,y2 = Q
    if x1 == x2:
        if (y1 + y2) % n == 0:
            return O, 1
        num = (3*x1*x1 + A) % n
        den = (2*y1) % n
    else:
        num = (y2 - y1) % n
        den = (x2 - x1) % n
    g = gcd(den, n)
    if g != 1:
        return None, g
    lam = num * inverse_mod(den, n) % n
    x3 = (lam*lam - x1 - x2) % n
    y3 = (lam*(x1 - x3) - y1) % n
    return (x3, y3), 1

def mul_chk(k, P):
    # left-to-right binary
    R = O
    for bit in bin(k)[2:]:
        R, g = add_chk(R, R)
        if g != 1: return None, g
        if bit == '1':
            R, g = add_chk(R, P)
            if g != 1: return None, g
    return R, 1

def ecf(B):
    P = G
    t0 = time.time()
    for q in prime_range(2, B+1):
        e = 1
        while q**(e+1) <= B: e += 1
        k = q**e
        P, g = mul_chk(k, P)
        if g != 1:
            print("FOUND factor at B=%d, prime q=%d: %d" % (B, q, g))
            print("cofactor:", n//g)
            return g
        if P == O:
            print("point became O mod n at B=%d q=%d" % (B,q)); return None
    print("B=%d done in %.1fs, no factor" % (B, time.time()-t0))
    return None

B = int(sys.argv[1]) if len(sys.argv)>1 else 100000
r = ecf(B)
