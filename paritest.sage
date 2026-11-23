from sage.libs.pari import pari
# small composite test: curve y^2=x^3+x+1 mod 15
n = 15
try:
    E = pari.ellinit([0,0,0,1,1], n)
    print("ellinit ok:", E)
    P = pari.ellmul(E, [0,1], 3)
    print("ellmul 3P:", P)
    P2 = pari.ellmul(E, [0,1], 5)
    print("ellmul 5P:", P2)
except Exception as e:
    print("ERROR:", type(e), e)
