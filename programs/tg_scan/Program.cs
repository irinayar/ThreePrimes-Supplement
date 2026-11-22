using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Threading.Tasks;

// Targeted scan of the comparison D 2^M <= 2^L at eta = log2 m + shift (shift = 0: eta = log2 m).
// For fixed m and a set B of c primes <= m with a_p = 1 (alpha = c, Delta = sum log2 p), the primes above m (a_p = 0) enter only through g = sum 1/sqrt(log2 p).
// For every target K of L = ceil(a_S (eta^2+eta)) put g_K = sqrt(K/(eta^2+eta)); y(g) = eta (g t*(g) - alpha) is increasing in g, so the best attainable g <= g_K gives the largest excess.
// U(K) = y(g_K) - (K - ceil(Delta)) (continuous g) is an upper bound for the excess margin; a violation needs U(K) > 0.
// Candidates (U(K) > thr) are evaluated exactly (256-bit fixed point) for the largest subset sum of the primes above m that fits under g_K - g_B.
class P {
  const int PREC = 256;
  static readonly BigInteger F = BigInteger.One << PREC;
  static BigInteger ISqrt(BigInteger n) { if (n.IsZero) return 0; int bl = (int)n.GetBitLength(); BigInteger x = BigInteger.One << ((bl + 1) / 2); while (true) { BigInteger y = (x + n / x) >> 1; if (y >= x) return x; x = y; } }
  static BigInteger SqrtFP(BigInteger x) => ISqrt(x * F);
  static BigInteger Log2FP(BigInteger x) {
    int k = (int)x.GetBitLength() - 1; BigInteger r = (x << PREC) >> k; BigInteger res = (BigInteger)k << PREC;
    for (int i = 1; i <= PREC; i++) { r = (r * r) >> PREC; if (r >= (F << 1)) { r >>= 1; res |= BigInteger.One << (PREC - i); } }
    return res;
  }
  static BigInteger CeilFP(BigInteger y) { if (y <= 0) return 0; return (y + F - 1) / F; }
  static double ToDouble(BigInteger fp) => (double)fp / (double)F;
  static ulong MulMod(ulong a, ulong b, ulong m) => (ulong)((UInt128)a * b % m);
  static ulong PowMod(ulong a, ulong e, ulong m) { ulong r = 1; a %= m; while (e > 0) { if ((e & 1) == 1) r = MulMod(r, a, m); a = MulMod(a, a, m); e >>= 1; } return r; }
  static readonly ulong[] SmallP = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };
  static bool IsPrime(ulong n) {
    if (n < 2) return false;
    foreach (ulong p in SmallP) { if (n % p == 0) return n == p; }
    ulong d = n - 1; int s = 0; while ((d & 1) == 0) { d >>= 1; s++; }
    foreach (ulong a in SmallP) {
      ulong x = PowMod(a, d, n); if (x == 1 || x == n - 1) continue; bool comp = true;
      for (int r = 1; r < s; r++) { x = MulMod(x, x, n); if (x == n - 1) { comp = false; break; } }
      if (comp) return false;
    }
    return true;
  }
  // exact excess Delta + M - L for the set: below primes (a=1) and above primes (a=0), at eta = log2 m + shift
  static BigInteger ExactExcess(ulong m, ulong[] below, ulong[] above, BigInteger shiftFP, out BigInteger Mout, out BigInteger Lout) {
    BigInteger eta = Log2FP(m) + shiftFP; int c = below.Length; BigInteger Dl = 0, A = 0;
    foreach (var p in below) { var l = Log2FP(p); Dl += l; A += (F * F) / SqrtFP(l); }
    foreach (var p in above) { var l = Log2FP(p); A += (F * F) / SqrtFP(l); }
    BigInteger A2 = (A * A) >> PREC; BigInteger aS = BigInteger.Max(F, A2); BigInteger e2 = (eta * eta) >> PREC;
    BigInteger Qt = ((e2 * A2) >> PREC) - 4 * (eta * c - Dl - eta); if (Qt < 0) Qt = 0;
    BigInteger ts = (((eta * A) >> PREC) + SqrtFP(Qt)) / 2; BigInteger t2 = (ts * ts) >> PREC; BigInteger y = t2 - eta - Dl; BigInteger M = CeilFP(y);
    BigInteger Lv = (((aS * e2) >> PREC) + ((aS * eta) >> PREC) + F - 1) / F;
    Mout = M; Lout = Lv; return Dl + (M << PREC) - (Lv << PREC);
  }
  class Stat { public long m, cands, exact, viol, pos; public double Umax = -1e9; public string UmaxArg = ""; public double exMax = -1e9; public string exArg = ""; public string firstViol = ""; }
  // Construction mode: given m, B = {largest prime <= m}; for K near the best continuous target choose d primes ABOVE m (any size) with sum 1/sqrt(log2 p) in (g_K - g_B - eps, g_K - g_B]
  static void Construct(ulong m, int d, int tries) {
    ulong pB = m; while (!IsPrime(pB)) pB--; double eta = Math.Log2((double)m); double w = eta * eta + eta; double lB = Math.Log2((double)pB); double gB = 1 / Math.Sqrt(lB); double Dl = lB; double cD = Math.Ceiling(Dl);
    Console.WriteLine($"m={m} B={pB} eta={eta:F9} w={w:F6} Delta={Dl:F9} ceil={cD}");
    double bestU = -1e9; long bestK = 0;
    for (long K = (long)Math.Ceiling(w); K < (long)Math.Ceiling(w) + 4; K++) { double gK = Math.Sqrt(K / w); double Q = eta * eta * gK * gK - 4 * (eta - Dl - eta + 0); Q = eta * eta * gK * gK - 4 * (eta * 1 - Dl - eta); double ts = (eta * gK + Math.Sqrt(Q)) / 2; double y = eta * (gK * ts - 1); double U = y - (K - cD); Console.WriteLine($"  K={K} g_K={gK:F9} U={U:F6} dy/dg~{eta * ts:F1}"); if (U > bestU) { bestU = U; bestK = K; } }
    if (bestU <= 0) { Console.WriteLine("no positive continuous margin"); return; }
    double gKb = Math.Sqrt(bestK / w); double target = gKb - gB; double eps = bestU / (eta * (eta + 1)) * 0.9; Console.WriteLine($"K={bestK} target sum of above-primes = {target:F9}, window eps={eps:E3}");
    var rnd = new Random(12345); int found = 0;
    for (int t = 0; t < tries && found < 3; t++) {
      var ps = new List<ulong>(); double sum = 0; bool ok = true;
      for (int i = 0; i < d - 1; i++) { double lam = eta + 0.05 + rnd.NextDouble() * 12; ulong q = (ulong)Math.Pow(2, lam); while (!IsPrime(q) || q <= m || ps.Contains(q)) q++; ps.Add(q); sum += 1 / Math.Sqrt(Math.Log2((double)q)); }
      double rem = target - eps * 0.5 - sum; if (rem <= 0) continue; double lam4 = 1 / (rem * rem); if (lam4 < eta + 0.001 || lam4 > 62) continue;
      ulong q4 = (ulong)Math.Pow(2, lam4); while (!IsPrime(q4) || q4 <= m || ps.Contains(q4)) q4++; ps.Add(q4);
      double g = gB + ps.Sum(q => 1 / Math.Sqrt(Math.Log2((double)q))); if (g > gKb || g < gKb - eps) continue;
      var e = ExactExcess(m, new[] { pB }, ps.ToArray(), 0, out var Mx, out var Lx);
      Console.WriteLine($"  set above={string.Join(",", ps)} g={g:F9} (g_K={gKb:F9}) M={Mx} L={Lx} exact excess Delta+M-L = {ToDouble(e):E4}"); if (e > 0) found++;
    }
    Console.WriteLine($"violations found: {found}");
  }
  static void Main(string[] args) {
    if (args[0] == "cx") { Construct(ulong.Parse(args[1]), int.Parse(args[2]), int.Parse(args[3])); return; }
    int jlo = int.Parse(args[0]), jhi = int.Parse(args[1]); int nUp = int.Parse(args[2]), nDown = int.Parse(args[3]); double shift = args.Length > 4 ? double.Parse(args[4], System.Globalization.CultureInfo.InvariantCulture) : 0.0;
    double thr = args.Length > 5 ? double.Parse(args[5], System.Globalization.CultureInfo.InvariantCulture) : -0.05; int NB = 6, NA = 10, maxC = 3;
    BigInteger shiftFP = ((BigInteger)(long)Math.Round(shift * 1e9) << PREC) / 1000000000;
    for (int j = jlo; j <= jhi; j++) {
      var rnd = new Random(7000 + j); double lo = Math.Pow(2, j) * (1 - 2.0 / j), mid = Math.Pow(2, j), hi = Math.Pow(2, j) * (1 + 2.5 / j);
      var ms = new List<ulong>(); for (int i = 0; i < nUp; i++) ms.Add((ulong)(mid + rnd.NextDouble() * (hi - mid))); for (int i = 0; i < nDown; i++) ms.Add((ulong)(lo + rnd.NextDouble() * (mid - lo)));
      var st = new Stat(); object lk = new object();
      Parallel.ForEach(ms, () => new Stat(), (m, state, loc) => {
        var below = new List<ulong>(); for (ulong q = m; below.Count < NB && q > 2; q--) if (IsPrime(q)) below.Add(q);
        var above = new List<ulong>(); for (ulong q = m + 1; above.Count < NA; q++) if (IsPrime(q)) above.Add(q);
        double eta = Math.Log2((double)m) + shift; double w = eta * eta + eta;
        double[] ib = below.Select(p => 1 / Math.Sqrt(Math.Log2((double)p))).ToArray(), ia = above.Select(p => 1 / Math.Sqrt(Math.Log2((double)p))).ToArray();
        // sorted subset sums of the above primes
        int na = above.Count; var sums = new (double s, int mask)[1 << na];
        for (int mk = 0; mk < (1 << na); mk++) { double s = 0; for (int i = 0; i < na; i++) if ((mk >> i & 1) == 1) s += ia[i]; sums[mk] = (s, mk); }
        Array.Sort(sums, (x, y) => x.s.CompareTo(y.s)); double[] sv = sums.Select(x => x.s).ToArray();
        loc.m++;
        for (int mb = 1; mb < (1 << below.Count); mb++) {
          int c = 0; double gB = 0, Dl = 0; for (int i = 0; i < below.Count; i++) if ((mb >> i & 1) == 1) { c++; gB += ib[i]; Dl += Math.Log2((double)below[i]); }
          if (c > maxC) continue; double cD = Math.Ceiling(Dl); double gmax = gB + sv[sv.Length - 1];
          long K0 = (long)Math.Ceiling(w);
          long Kmax = Math.Max(K0, (long)Math.Ceiling(gmax * gmax * w));
          for (long K = K0; K <= Kmax; K++) {
            double gK = Math.Sqrt(K / w);
            if (gK < gB) continue; // even the empty subset has g = gB > g_K: not attainable
            double Q = eta * eta * gK * gK - 4 * (eta * c - Dl - eta); if (Q < 0) continue; double ts = (eta * gK + Math.Sqrt(Q)) / 2; double y = eta * (gK * ts - c);
            double U = y - (K - cD); if (U > 0) loc.pos++; if (U > loc.Umax) { loc.Umax = U; loc.UmaxArg = $"j={j} m={m} c={c} mb={mb} K={K}"; }
            if (U <= thr) continue; loc.cands++;
            // largest attainable subset sum <= gK - gB
            double bound = gK - gB; int lo2 = 0, hi2 = sv.Length - 1, pos = -1; while (lo2 <= hi2) { int mid2 = (lo2 + hi2) / 2; if (sv[mid2] <= bound + 1e-12) { pos = mid2; lo2 = mid2 + 1; } else hi2 = mid2 - 1; }
            for (int dpos = 0; dpos < 3 && pos - dpos >= 0; dpos++) {
              int ma = sums[pos - dpos].mask; var bs = new List<ulong>(); for (int i = 0; i < below.Count; i++) if ((mb >> i & 1) == 1) bs.Add(below[i]); var asl = new List<ulong>(); for (int i = 0; i < na; i++) if ((ma >> i & 1) == 1) asl.Add(above[i]);
              var e = ExactExcess(m, bs.ToArray(), asl.ToArray(), shiftFP, out var Mx, out var Lx); double ed = ToDouble(e); loc.exact++;
              if (ed > loc.exMax) { loc.exMax = ed; loc.exArg = $"m={m} c={c} d={asl.Count} mb={mb} ma={ma} K={K} M={Mx} L={Lx}"; }
              if (e > 0) { loc.viol++; if (loc.firstViol == "") loc.firstViol = $"VIOLATION m={m} below=[{string.Join(",", bs)}] above=[{string.Join(",", asl)}] M={Mx} L={Lx} excess={ed:E4}"; }
            }
          }
        }
        return loc;
      }, loc => { lock (lk) { st.m += loc.m; st.cands += loc.cands; st.exact += loc.exact; st.viol += loc.viol; st.pos += loc.pos; if (loc.Umax > st.Umax) { st.Umax = loc.Umax; st.UmaxArg = loc.UmaxArg; } if (loc.exMax > st.exMax) { st.exMax = loc.exMax; st.exArg = loc.exArg; } if (st.firstViol == "") st.firstViol = loc.firstViol; } });
      Console.WriteLine($"j={j} shift={shift}: m-samples={st.m} candidates={st.cands} exact={st.exact} violations={st.viol} (m,B,K) with continuous U>0: {st.pos} | max U (continuous g) = {st.Umax:E3} at {st.UmaxArg} | max exact excess = {st.exMax:E3} at {st.exArg}");
      if (st.firstViol != "") Console.WriteLine("  " + st.firstViol);
    }
  }
}
