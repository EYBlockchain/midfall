import re, time, sys
from sage.libs.pari import pari
A = 0x1115160ded643518fc0b46ad430da8e5c15f85fe03d0b6b181060f8c167714c650b31b4850b2f06430903acabcee293a8f88eb2a94554636fe823e6b6e753f7de3b6436b32518715df94030bf910993d5158cf47c83042e3fff16181819155f4
n = 839268999099425968807411462926249098389252581409067470253664485759322114291073830711064449642314699377238366107656217249459455592803416447657121161867800269745726650461218600418110039592265036637486587632551853112632091434362413211
Gx=0x858cd5e8856db40d611f0c8a605296b64146118a5112bd5f25333eecbcb0b22ba689491990304ac0c709e99af8cc0c789131f940ec79936f4c75a24ef7165eb1e53f0ffb46a931d2ec95ba678b5825cb3649ab4d4e4b206dcbc62236fefa3bc1
Gy=0x461e32608d4000477828abe7e900882d9864d3792b38a332b6fab213a9bf840fe3cb7b3be185266143c493e8d10d9cf37ea8f90695b7e6bdc17938cb7d11dd4e40f7f4037e9e0e3307e4e1de207f56a51e62eab3bb21ca6ebbc3f9bc8e4be604
Bcoef=(Gy^2-Gx^3-A*Gx)%n
E = pari.ellinit([0,0,0,A,Bcoef], n)
P = [Gx,Gy]
B = int(sys.argv[1]) if len(sys.argv)>1 else 1200000
e = int(sys.argv[2]) if len(sys.argv)>2 else 4
primes = list(prime_range(2, B+1))
print("B=%d e=%d, %d primes" % (B,e,len(primes)), flush=True)
t0=time.time()
for i,q in enumerate(primes):
    try:
        P = pari.ellmul(E, P, Integer(q)**e)
    except Exception as ex:
        s=str(ex)
        m=re.search(r'Mod\((\d+),\s*(\d+)\)', s)
        print("FAILURE at i=%d prime=%d time=%.1f" % (i,q,time.time()-t0), flush=True)
        print("msg:", s[:300], flush=True)
        if m:
            d=int(m.group(1)); N=int(m.group(2)); g=gcd(d,N)
            print("FACTOR =", g, flush=True)
            print("COFACTOR =", n//g, flush=True)
        break
    if i % 10000 == 0:
        print("i=%d q=%d elapsed=%.1f" % (i,q,time.time()-t0), flush=True)
else:
    print("NO FACTOR up to B=%d in %.1fs" % (B,time.time()-t0), flush=True)
