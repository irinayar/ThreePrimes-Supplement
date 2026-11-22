using System;
using System.Linq;
using System.Numerics;
// Independent check at eta = log2 m EXACTLY (default: m = 66922, S = {66919, 4864529, 52655459, 67477043, 272962260021097}; or give m and the primes as arguments). Trial-division primality, a_p from the definition, double precision (margins >> rounding), and the exact integer comparison D*2^M > 2^L.
class P {
  static bool IsPrime(long n) { if (n < 2) return false; if (n % 2 == 0) return n == 2; for (long d = 3; d * d <= n; d += 2) if (n % d == 0) return false; return true; }
  static void Main() {
    long m = 66922; long[] S = { 66919, 4864529, 52655459, 67477043, 272962260021097 };
    string[] A = Environment.GetCommandLineArgs().Skip(1).ToArray(); if (A.Length >= 2) { m = long.Parse(A[0]); S = A.Skip(1).Select(long.Parse).ToArray(); }
    foreach (var p in S) Console.WriteLine($"{p} prime={IsPrime(p)}");
    // a_p = min{a >= 0 : p^-(2a+1) < 1/m}  <=>  p^(2a+1) > m
    var a = S.Select(p => { int aa = 0; while (BigInteger.Pow(p, 2 * aa + 1) <= m) aa++; return aa; }).ToArray();
    Console.WriteLine("a_p = " + string.Join(",", a));
    double eta = Math.Log2(m); double g = S.Sum(p => 1 / Math.Sqrt(Math.Log2(p))); double aS = Math.Max(1, g * g);
    double alpha = a.Sum(); double Dl = 0; for (int i = 0; i < S.Length; i++) Dl += (double)a[i] * a[i] * Math.Log2(S[i]);
    double L0 = aS * (eta * eta + eta); long L = (long)Math.Ceiling(L0);
    double Q = eta * eta * g * g - 4 * (eta * alpha - Dl - eta); double ts = (eta * g + Math.Sqrt(Q)) / 2; double y = ts * ts - eta - Dl; long M = Math.Max(0, (long)Math.Ceiling(y));
    Console.WriteLine($"eta=log2 m={eta:F12} g={g:F12} g^2={g * g:F12} a_S={aS:F12} alpha={alpha} Delta={Dl:F12} ceil(Delta)={Math.Ceiling(Dl)}");
    Console.WriteLine($"a_S(eta^2+eta)={L0:F9} L={L}; Q={Q:F9} t*={ts:F9} y=t*^2-eta-Delta={y:F9} M={M}; y - (L - ceil(Delta)) = {y - (L - Math.Ceiling(Dl)):F9}");
    Console.WriteLine($"Delta+M-L = {Dl + M - L:F9}  =>  D*2^M/2^L = {Math.Pow(2, Dl + M - L):F9}");
    // exact: D = prod p^(a_p^2) = 66919; D*2^M > 2^L ?
    BigInteger D = 1; for (int i = 0; i < S.Length; i++) D *= BigInteger.Pow(S[i], a[i] * a[i]);
    Console.WriteLine($"D={D}; D*2^M > 2^L : {D * BigInteger.Pow(2, (int)M) > BigInteger.Pow(2, (int)L)}");
    // eta alpha - Delta and open-region test
    Console.WriteLine($"eta*alpha={eta * alpha:F9} < ceil(Delta)={Math.Ceiling(Dl)} : {eta * alpha < Math.Ceiling(Dl)}; m<=2^eta (equality); m*delta=1 with delta=1/m");
  }
}
