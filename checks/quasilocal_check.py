"""Checks of the quasi-local construction on a finite window W of sites (see README.md).
Conventions.  Sites 0..n-1, alphabet sizes q[u]; configuration = tuple s; F = all configs on W,
H = C^F with basis index = mixed-radix rank of s (site 0 most significant).
Local space of X (sorted tuple): letters eta = tuple (eta_x)_{x in X sorted}, same ranking.
iota_X(m) is defined by its action  (iota_X(m) psi)(s) = sum_xi m(s|X, xi) psi(glue X xi s),
so its matrix is  [s, glue X xi s] = m(s|X, xi)  (row s, column glue).  This is compared with
embed X m (s,s') = [s agrees s' off X] m(s|X, s'|X) from LocalAlgebrasLean/Qudit/Config.lean,
computed separately.
Entries: Gaussian integers stored in complex128 (all values < 2^53, so arithmetic is exact);
equalities are asserted with exact array equality.  The operator-norm, rank and distance
comparisons go through singular values and use a tolerance of 1e-9.  The random choices are
seeded, so every run prints the same output.
"""
import itertools, random
import numpy as np

rng = np.random.default_rng(20261006)
random.seed(1)

def configs(q):  return list(itertools.product(*[range(k) for k in q]))
def rank(q, s):
    r = 0
    for k, a in zip(q, s): r = r * k + a
    return r
def restrict(X, s): return tuple(s[x] for x in X)
def glue(X, xi, s):
    t = list(s)
    for x, a in zip(X, xi): t[x] = a
    return tuple(t)
def agrees_off(X, s, t): return all(s[u] == t[u] for u in range(len(s)) if u not in X)

def rand_m(dim):
    return (rng.integers(-3, 4, (dim, dim)) + 1j * rng.integers(-3, 4, (dim, dim))).astype(complex)

def local_configs(q, X): return list(itertools.product(*[range(q[x]) for x in X]))
def local_dim(q, X):
    d = 1
    for x in X: d *= q[x]
    return d

def iota(q, X, m):
    """matrix of iota_X(m) via the action on psi: entry [s, glue X xi s] += m(s|X, xi)."""
    F = configs(q); N = len(F); LX = local_configs(q, X)
    idx = {eta: i for i, eta in enumerate(LX)}
    M = np.zeros((N, N), complex)
    for s in F:
        a = idx[restrict(X, s)]
        for xi in LX:
            M[rank(q, s), rank(q, glue(X, xi, s))] += m[a, idx[xi]]
    return M

def embed(q, X, m):
    """Config.lean: (embed X m) s s' = [AgreesOff X s s'] m (s|X) (s'|X)."""
    F = configs(q); N = len(F); idx = {eta: i for i, eta in enumerate(local_configs(q, X))}
    M = np.zeros((N, N), complex)
    for s in F:
        for t in F:
            if agrees_off(X, s, t):
                M[rank(q, s), rank(q, t)] = m[idx[restrict(X, s)], idx[restrict(X, t)]]
    return M

def eq(a, b): return bool(np.array_equal(a, b))
def dag(a): return a.conj().T

def tensor_ext(q, X, Y, m):
    """m (on X, sorted) tensor identity on Y minus X, as a matrix on the letters of Y (sorted):
    kron(m, 1_Z) with Z = Y minus X sorted, tensor-factor order (X sites, then Z sites), then
    the axes are permuted to Y-sorted site order."""
    Z = [y for y in Y if y not in X]
    dz = local_dim(q, Z)
    K = np.kron(m, np.eye(dz, dtype=complex))
    order = list(X) + Z
    dims = [q[u] for u in order]
    n = len(order)
    K = K.reshape(dims + dims)
    perm = [order.index(y) for y in Y]
    K = K.transpose(perm + [p + n for p in perm])
    d = local_dim(q, Y)
    return K.reshape(d, d)

def subsets(n):
    for r in range(n + 1):
        for X in itertools.combinations(range(n), r): yield X

def run_main(q, tag, nsub):
    n = len(q); N = int(np.prod(q))
    subs = list(subsets(n)); random.shuffle(subs)
    subs = subs[:nsub]
    one = np.eye(N, dtype=complex)
    cnt = {k: 0 for k in "12345"}
    for X in subs:
        d = local_dim(q, X)
        a, b = rand_m(d), rand_m(d)
        ia, ib = iota(q, X, a), iota(q, X, b)
        # 1: unital star homomorphism
        assert eq(iota(q, X, a @ b), ia @ ib)
        assert eq(iota(q, X, dag(a)), dag(ia))
        assert eq(iota(q, X, np.eye(d, dtype=complex)), one)
        assert eq(iota(q, X, a + 2 * b), ia + 2 * ib)
        cnt["1"] += 1
        # 2: injective (explicit left inverse at the reference config s0 = 0) and isometric
        s0 = tuple(0 for _ in q); LX = local_configs(q, X)
        rec = np.array([[ia[rank(q, glue(X, e, s0)), rank(q, glue(X, f, s0))] for f in LX] for e in LX])
        assert eq(rec, a)
        na, nia = np.linalg.norm(a, 2), np.linalg.norm(ia, 2)
        assert abs(na - nia) < 1e-9 * max(1, na)
        cnt["2"] += 1
        # 5: agrees with embed
        assert eq(ia, embed(q, X, a)); cnt["5"] += 1
        # 3: compatibility for supersets Y
        for Y in subs:
            if set(X) <= set(Y):
                assert eq(iota(q, Y, tensor_ext(q, X, Y, a)), ia); cnt["3"] += 1
        # 4: disjoint commutation
        for Y in subs:
            if not set(X) & set(Y):
                c = rand_m(local_dim(q, Y)); ic = iota(q, Y, c)
                assert eq(ia @ ic, ic @ ia); cnt["4"] += 1
    print(f"[{tag}] q={q} N={N} subsets tested={len(subs)} counts={cnt}")

def perm_unitary(q, pi):
    """U|s> = |pi.s>, (pi.s)(pi u) = s(u); needs q[pi u] = q[u]."""
    F = configs(q); N = len(F); U = np.zeros((N, N), complex)
    for s in F:
        t = [0] * len(s)
        for u in range(len(s)): t[pi[u]] = s[u]
        U[rank(q, tuple(t)), rank(q, s)] = 1
    return U

def run_perm(q, tag, trials=12):
    n = len(q); assert len(set(q)) == 1
    nonsym = 0
    for _ in range(trials):
        pi = list(range(n)); random.shuffle(pi)
        U = perm_unitary(q, pi)
        assert eq(U @ dag(U), np.eye(len(U), dtype=complex))
        X = tuple(sorted(random.sample(range(n), random.randint(0, n))))
        m = rand_m(local_dim(q, X))
        piX = tuple(sorted(pi[x] for x in X))      # image set, as in O -> gO = {x : g^-1 x in O}
        LX = local_configs(q, X); LpX = local_configs(q, piX); idp = {e: i for i, e in enumerate(LpX)}
        def move(eta):
            dd = {pi[x]: a for x, a in zip(X, eta)}
            return tuple(dd[y] for y in piX)
        mp = np.zeros_like(m)                      # m'(eta', zeta') = m(eta, zeta), eta'(pi u) = eta(u)
        for i, e in enumerate(LX):
            for j, f in enumerate(LX): mp[idp[move(e)], idp[move(f)]] = m[i, j]
        assert eq(U @ iota(q, X, m) @ dag(U), iota(q, piX, mp))
        # the reverse conjugation U^dag . U is the action of pi^-1, i.e. targets pi^-1 X
        piinv = [0] * n
        for u in range(n): piinv[pi[u]] = u
        assert eq(dag(U), perm_unitary(q, piinv))
        if len(X) and len(X) < n and piX != X:
            nonsym += 1
            assert not eq(iota(q, X, m), iota(q, piX, mp)) or not m.any()
    print(f"[{tag}] permutation covariance: {trials} random pi, q={q}: "
          f"U iota_X(m) U^dag = iota_piX(m') ({nonsym} with piX != X)")

print("== main checks 1-5 ==")
run_main((2, 2, 2, 2, 2, 2), "W=6, q=2", 14)
run_main((3, 3, 3, 3), "W=4, q=3", 16)
run_main((2, 3, 2, 3, 2), "W=5, mixed alphabets", 16)
print("== check 6 (permutations) ==")
run_perm((2,) * 6, "W=6 q=2")
run_perm((3,) * 4, "W=4 q=3")

print("== 7 degenerate section ==")
for q in [(2, 3, 2), (1, 1, 1), (2,)]:
    N = int(np.prod(q)); c = complex(2, -3)
    assert eq(iota(q, (), np.array([[c]])), c * np.eye(N, dtype=complex))
    assert eq(embed(q, (), np.array([[c]])), c * np.eye(N, dtype=complex))
print("X empty: iota(c) = c 1 : ok (q=(2,3,2),(1,1,1),(2,))")
q = (3, 2, 3)
for x in range(3):
    m = rand_m(q[x]); I = iota(q, (x,), m)
    K = [np.eye(k, dtype=complex) for k in q]; K[x] = m
    assert eq(I, np.kron(np.kron(K[0], K[1]), K[2]))
    assert eq(I, embed(q, (x,), m))
print("single site: iota_{x}(m) = site-ordered Kronecker product 1 x m x 1 : ok")
q = (1, 1, 1, 1)
for X in subsets(4):
    m = rand_m(1); n2 = rand_m(1)
    assert eq(iota(q, X, m), m)
    assert eq(iota(q, X, m @ n2), iota(q, X, m) @ iota(q, X, n2))
q = (1, 2, 1, 3)
for X in subsets(4):
    d = local_dim(q, X); m = rand_m(d)
    assert eq(iota(q, X, m), embed(q, X, m))
    X2 = tuple(x for x in X if q[x] > 1)
    assert local_dim(q, X2) == d and eq(iota(q, X, m), iota(q, X2, m))
print("alphabet size 1: all-trivial window gives 1-dim H, iota_X(m) = m; trivial sites are invisible: ok")
for q in [(2, 2, 2), (3, 2, 3), (1, 2)]:
    d = int(np.prod(q)); m = rand_m(d); W = tuple(range(len(q)))
    assert eq(iota(q, W, m), m) and eq(embed(q, W, m), m)
    assert abs(np.linalg.norm(m, 2) - np.linalg.norm(iota(q, W, m), 2)) < 1e-9 * np.linalg.norm(m, 2)
print("X = W: iota_W(m) = m : ok")
q = (2, 3, 2)
for X in [(), (0,), (1,), (0, 2), (0, 1, 2)]:
    d = local_dim(q, X); cols = []
    for i in range(d):
        for j in range(d):
            e = np.zeros((d, d), complex); e[i, j] = 1; cols.append(iota(q, X, e).ravel())
    assert np.linalg.matrix_rank(np.array(cols).T) == d * d
print("injectivity (full column rank of m -> iota_X(m)) for q=(2,3,2): ok")
print("== 8 independence of the reference configuration (transport of local embeddings) ==")
def rand_perm_with(k, a, b):
    """random permutation pi of range(k) with pi[a] = b."""
    rest = [x for x in range(k) if x != a]; imgs = [x for x in range(k) if x != b]
    random.shuffle(imgs)
    pi = [0] * k; pi[a] = b
    for x, y in zip(rest, imgs): pi[x] = y
    return pi

def run_ref(q, s0, s1, tag, nsub=40):
    n = len(q); F = configs(q); N = len(F)
    pis = [rand_perm_with(q[u], s0[u], s1[u]) for u in range(n)]
    ap = lambda s: tuple(pis[u][s[u]] for u in range(n))
    W = np.zeros((N, N), complex)
    for s in F: W[rank(q, ap(s)), rank(q, s)] = 1
    assert eq(W @ dag(W), np.eye(N, dtype=complex)) and eq(dag(W) @ W, np.eye(N, dtype=complex))
    assert ap(s0) == tuple(s1)                                  # W e_{s0} = e_{s0'}
    assert W[rank(q, s1), rank(q, s0)] == 1
    ndiff = sum(a != b for a, b in zip(s0, s1))
    allsub = list(subsets(n)); random.shuffle(allsub); subs = allsub[:nsub]
    if () not in subs: subs.append(())
    if tuple(range(n)) not in subs: subs.append(tuple(range(n)))
    for X in subs:
        LX = local_configs(q, X); idx = {e: i for i, e in enumerate(LX)}
        d = len(LX); m = rand_m(d)
        # (pi_* m)(pi_X eta, pi_X zeta) = m(eta, zeta)
        mp = np.zeros_like(m)
        for e in LX:
            pe = tuple(pis[x][a] for x, a in zip(X, e)); i = idx[pe]
            for f in LX:
                pf = tuple(pis[x][a] for x, a in zip(X, f)); mp[i, idx[pf]] = m[idx[e], idx[f]]
        assert eq(W @ iota(q, X, m) @ dag(W), iota(q, X, mp))
        assert eq(W @ iota(q, X, m) @ dag(W), embed(q, X, mp))
    print(f"[{tag}] q={q} s0={tuple(s0)} s0'={tuple(s1)} differ at {ndiff} site(s): "
          f"W iota_X(m) W* = iota'_X(pi_* m) on {len(subs)} subsets: ok")

for q in [(2, 3, 2, 3), (3, 2, 3, 2, 2), (2, 2, 3)]:
    n = len(q)
    s0 = tuple(random.randrange(k) for k in q)
    def differ_at(S):
        return tuple(((s0[u] + 1 + random.randrange(q[u] - 1)) % q[u]) if u in S else s0[u] for u in range(n))
    run_ref(q, s0, s0, "ref: identical", 20)
    run_ref(q, s0, differ_at({random.randrange(n)}), "ref: one site")
    run_ref(q, s0, differ_at(set(random.sample(range(n), 2))), "ref: two sites")
    run_ref(q, s0, differ_at(set(range(n))), "ref: every site")
print("ref independence (finite window: F = F' = all configurations, so only W's form is tested): ok")

print("== 9 distance from the reference projection to the local algebras, finite-window illustration ==")
print("NOTE: a finite window can only ILLUSTRATE the bound; the infinite-volume statement is not tested here.")
print("Per proper X: lower bound by an explicit functional phi = (<psi0|.|psi0> - <psi1|.|psi1>)/2 of norm <= 1,")
print("psi0 = e_{s0}, psi1 = e_t (t = s0 with letter 1 at u not in X), phi(iota_X(m)) = 0 exactly, phi(P) = 1/2;")
print("upper bound by m = E/2 (SVD, tolerance 1e-9); and random search near E/2 as a sanity floor.")
mind = None; mindim = None
for n in range(2, 8):
    q = (2,) * n; N = 2 ** n; s0 = (0,) * n
    e0 = np.zeros(N, complex); e0[rank(q, s0)] = 1
    P = np.outer(e0, e0)
    Xs = [tuple(x for x in range(n) if x != u) for u in range(n)]          # window minus one site
    if n <= 5: Xs += [X for X in subsets(n) if len(X) < n - 1 and random.random() < 0.3]
    for X in Xs:
        u = [v for v in range(n) if v not in X][0]
        t = tuple(1 if v == u else 0 for v in range(n)); e1 = np.zeros(N, complex); e1[rank(q, t)] = 1
        LX = local_configs(q, X); d = len(LX)
        E = np.zeros((d, d), complex); E[LX.index(restrict(X, s0)), LX.index(restrict(X, s0))] = 1
        m = rand_m(d); im = iota(q, X, m)
        assert (e0 @ im @ e0) - (e1 @ im @ e1) == 0                   # phi kills iota_X(M_X), exactly
        assert (e0 @ P @ e0) - (e1 @ P @ e1) == 1                     # phi(P) = 1/2 after dividing by 2
        up = np.linalg.norm(P - iota(q, X, E / 2), 2)
        assert abs(up - 0.5) < 1e-9
        best = up
        for _ in range(6):
            mm = E / 2 + 0.05 * (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) * rng.random()
            best = min(best, np.linalg.norm(P - iota(q, X, mm), 2))
        assert best >= 0.5 - 1e-9
        if mind is None or best < mind: mind, mindim = best, (n, X)
    print(f"window n={n}: {len(Xs)} proper subsets, lower bound 1/2 (exact functional), "
          f"witness distance {up:.12f}, min over search so far {mind:.12f}")
assert mind >= 0.5 - 1e-9
print(f"minimum distance found over all windows/subsets: {mind:.12f} (at n,X={mindim}); bound 1/2 holds (>= 1/2 - 1e-9)")

print("ALL ASSERTS PASSED")
