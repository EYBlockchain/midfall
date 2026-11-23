p = 21448884629509455597215930748900681159323242237303782800136123960324312583790994045488533691889446581945518026508097
q = 39128794508258790515072383975390806261898062361839764511933549761670978999997096053314214965077731424736773956742363
n=p*q
Cp = (p-1)//(2^6*3*23*3359)
Cq = (q-1)//(2*3*41*167*228113)
Cp1 = (p+1)//(2*7*13*1993)
Cq1 = (q+1)//(2^2*15881*35291*263503)
for nm,v in [("Cp",Cp),("Cq",Cq),("Cp+1",Cp1),("Cq+1",Cq1)]:
    print(nm, "bits", v.nbits(), "digits", len(str(v)), "pseudoprime", is_pseudoprime(v))
print()
print("p hex =", hex(p))
print("q hex =", hex(q))
print()
print("p mod small:", p % 3, p % 5, p % 7, p % 11)
print("q mod small:", q % 3, q % 5, q % 7, q % 11)
# check if p,q related to powers of 2
print("p / 2^383 =", float(p)/2**383)
print("q / 2^383 =", float(q)/2**383)
print("n / 2^767 =", float(n)/2**767)
