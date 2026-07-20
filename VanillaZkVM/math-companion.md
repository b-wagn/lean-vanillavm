# Mathematical Companion — `memory-integration`

A precise, math-form description of everything **defined** and **proven** in the
`VanillaZkVM` development on this branch. Each item names its Lean counterpart so
the two can be read side by side. The development is *perfect* and
*probability-free*: every security notion is stated as "the bad event never
happens", so all reductions are pointwise implications with no advantages, union
bounds, or security parameter.

**Files, bottom-up.** `Crypto.lean` (generic crypto) → `Zkvm.lean` (abstract VM +
correct-trace extractability) → `Memory.lean` (memory extractability) →
`Twostep.lean` (a concrete two-layer instance) and `Bus.lean` (the bus-delegated
leaf layer, an independent instance).

**Notation.**
A *full* VM state is $S = (S.\mathsf{pc},\, S.\mathsf{regs},\, S.\mathsf{mem})$ with
$\mathsf{regs} : \mathbb{N} \to \mathsf{Word}$.
A *committed* state is $\hat S = (\hat S.\mathsf{pc},\, \hat S.\mathsf{regs},\, \hat S.\widehat{\mathsf{mem}})$,
identical except memory is replaced by a commitment value.
For a vector commitment $\mathsf{VC}$ we write $\mathsf{cm}(m)=\mathsf{VC.commit}(m)$,
$\mathsf{op}(m,i)=\mathsf{VC.openProof}(m,i)$, and
$\mathsf{Vf}(C,i,v,\pi)=\mathsf{VC.verify}(C,i,v,\pi)$.

---

## 1. Generic cryptography (`Crypto.lean`)

### Definitions

**Relation.** A relation is a triple $R=(\mathsf{Stmt}, \mathsf{Wit}, \mathrm{rel})$ with
$\mathrm{rel} : \mathsf{Stmt} \to \mathsf{Wit} \to \mathsf{Prop}$. We write $R.\mathrm{rel}(x,w)$ for $(x;w)\in R$.

**Argument system.** For a relation $R$, an argument system is
$\mathsf{AS}=(\mathsf{Proof}, \mathsf{verify})$ with $\mathsf{verify} : \mathsf{Stmt}\to\mathsf{Proof}\to\mathsf{Prop}$.
Only the verifier is modeled (the prover is irrelevant to soundness).

**Extractor.** $E : \mathsf{Stmt}\to\mathsf{Proof}\to\mathsf{Wit}$ (straight-line: no rewinding, no adversary code).

**Knowledge soundness.**
$$
\mathsf{KS}(\mathsf{AS}) \;:=\; \exists E,\ \forall x\,p,\quad \mathsf{AS.verify}(x,p) \;\Rightarrow\; R.\mathrm{rel}\bigl(x, E(x,p)\bigr).
$$

**Vector commitment.** $\mathsf{VC}=(\mathsf{Value},\mathsf{Index},\mathsf{Com},\mathsf{OpenProof},\mathsf{commit},\mathsf{openProof},\mathsf{verify})$,
where $\mathsf{commit}:(\mathsf{Index}\to\mathsf{Value})\to\mathsf{Com}$ and
$\mathsf{verify}:\mathsf{Com}\to\mathsf{Index}\to\mathsf{Value}\to\mathsf{OpenProof}\to\mathsf{Prop}$.

**Position binding.**
$$
\mathsf{PB}(\mathsf{VC}) \;:=\; \forall C,i,v,v',\pi,\pi',\quad \mathsf{Vf}(C,i,v,\pi)\wedge \mathsf{Vf}(C,i,v',\pi') \;\Rightarrow\; v=v'.
$$

**Punctured binding.**  With one shared opening $\pi$ accepted at position $a$ under two commitments $C, C'$, they agree at every other position:
$$
\mathsf{PuB}(\mathsf{VC}) \;:=\; \forall\, C,C',a,v,v',\pi,\ i,u,u',\rho,\rho',\quad
\begin{aligned}
&\mathsf{Vf}(C,a,v,\pi)\wedge \mathsf{Vf}(C',a,v',\pi)\ \wedge\\
&\mathsf{Vf}(C,i,u,\rho)\wedge \mathsf{Vf}(C',i,u',\rho')\ \wedge\ i\neq a
\end{aligned}
\;\Rightarrow\; u=u'.
$$

**Hash commitment / collision resistance.** $H=(\mathsf{Domain},\mathsf{Digest},\mathsf{hash})$, and
$$
\mathsf{CR}(H) \;:=\; \forall b,b',\quad H.\mathsf{hash}(b)=H.\mathsf{hash}(b') \Rightarrow b=b'\qquad(\text{i.e. } \mathsf{hash}\text{ injective}).
$$

*Nothing is proven in this file — it is the vocabulary.* On this branch, unlike
`main`, $\mathsf{PB}$ and $\mathsf{PuB}$ are no longer inert: they are consumed in §3.

---

## 2. Abstract zkVM and correct-trace extractability (`Zkvm.lean`)

### Definitions

**VM states.** $\mathsf{Word}=\mathsf{Addr}=\mathsf{Byte}=\mathbb{N}$;
$\mathsf{VMStateWith}(M)$ is $(\mathsf{pc}:\mathsf{Word},\ \mathsf{regs}:\mathbb N\to\mathsf{Word},\ \mathsf{mem}:M)$;
$\mathsf{VMState}=\mathsf{VMStateWith}(\mathsf{Addr}\to\mathsf{Byte})$ and
$\mathsf{CommittedVMState}(\mathsf{VC})=\mathsf{VMStateWith}(\mathsf{VC.Com})$.

**Abstract zkVM.** $V=(\mathsf{State},\ \mathsf{step},\ T,\ \mathsf{Stmt},\ \mathsf{initial},\ \mathsf{terminal},\ \mathsf{Proof},\ \mathsf{verify})$,
with $\mathsf{step}:\mathsf{State}\to\mathsf{State}\to\mathsf{Prop}$, fixed step count $T\in\mathbb N$,
$\mathsf{initial},\mathsf{terminal}:\mathsf{Stmt}\to\mathsf{State}$, and $\mathsf{verify}:\mathsf{Stmt}\to\mathsf{Proof}\to\mathsf{Prop}$.

**Trace validity.** For $x:\mathsf{Stmt}$ and $tr:\mathbb N\to\mathsf{State}$,
$$
\mathsf{TraceValid}(x,tr) \;:=\; tr(0)=\mathsf{initial}(x)\ \wedge\ tr(T)=\mathsf{terminal}(x)\ \wedge\ \forall i<T,\ \mathsf{step}\bigl(tr(i),tr(i{+}1)\bigr).
$$

**Correct-execution relation & final argument system.**
$R^\star := (\mathsf{Stmt},\ \mathbb N\to\mathsf{State},\ \mathsf{TraceValid})$, and
$\mathsf{AS}^\star := (\mathsf{Proof},\ \mathsf{verify})$ viewed as an argument system for $R^\star$.

**Correct-trace extractability.**
$$
\mathsf{CTE}(V) \;:=\; \exists\, E:\mathsf{Stmt}\to\mathsf{Proof}\to(\mathbb N\to\mathsf{State}),\ \forall x\,p,\quad \mathsf{verify}(x,p)\Rightarrow \mathsf{TraceValid}\bigl(x,E(x,p)\bigr).
$$

**Trace concatenation.** For $N_{\mathrm{seg}}\in\mathbb N$, boundaries $d:\mathbb N\to\mathsf{State}$, and segments $seg:\mathbb N\to\mathbb N\to\mathsf{State}$,
$\mathsf{concatTrace}\,N_{\mathrm{seg}}\,d\,seg$ glues $m$ sub-chains into one length-$m N_{\mathrm{seg}}$ trace (defined by recursion on $m$).

### Theorems

**Keystone equivalence** (`cte_iff_knowledgeSound`).
$$
\boxed{\ \mathsf{CTE}(V) \iff \mathsf{KS}(\mathsf{AS}^\star(V))\ }
$$
*Proof.* Both sides unfold to "$\exists$ extractor, $\forall$ accepting $(x,p)$, the output is a valid trace"; they differ only in packaging $E$ as a bare function vs. an `Extractor` record. Structural. $\square$

**Flattening** (`chain_flatten`).
Let $N_{\mathrm{seg}}>0$. If for all $i<m$:
$seg\,i\,0=d\,i$, $\ seg\,i\,N_{\mathrm{seg}}=d(i{+}1)$, and $\forall j<N_{\mathrm{seg}},\ \mathsf{step}\bigl(seg\,i\,j,\ seg\,i\,(j{+}1)\bigr)$,
then with $C:=\mathsf{concatTrace}\,N_{\mathrm{seg}}\,d\,seg\,m$,
$$
C(0)=d(0),\qquad C(m N_{\mathrm{seg}})=d(m),\qquad \forall k<m N_{\mathrm{seg}},\ \mathsf{step}\bigl(C(k),C(k{+}1)\bigr).
$$
*Proof.* Induction on $m$; the seam case $k=nN_{\mathrm{seg}}$ crosses two segments. Treating $nN_{\mathrm{seg}}$ as an opaque atom keeps all side conditions linear, discharged by `omega`. $\square$

---

## 3. Memory extractability (`Memory.lean`)

This is the mathematical heart of the branch, and the first place $\mathsf{PB}$ and $\mathsf{PuB}$ do work.

### Definitions

**Full-memory state.** $\mathsf{FullVMState}(\mathsf{VC}) := \mathsf{VMStateWith}(\mathsf{VC.Index}\to\mathsf{VC.Value})$.
(The classic $\mathsf{VMState}$ is the instance $\mathsf{Index}=\mathsf{Value}=\mathbb N$.)

**Completeness** (the one new assumption).
$$
\mathsf{Complete}(\mathsf{VC}) \;:=\; \forall m,i,\quad \mathsf{Vf}\bigl(\mathsf{cm}(m),\ i,\ m(i),\ \mathsf{op}(m,i)\bigr)\qquad(\text{honest openings verify}).
$$

**Commitment invariant** (links a committed state to a full one).
$$
\mathsf{CommitInv}(\hat S, S) \;:=\; \hat S.\mathsf{pc}=S.\mathsf{pc}\ \wedge\ \hat S.\mathsf{regs}=S.\mathsf{regs}\ \wedge\ \hat S.\widehat{\mathsf{mem}}=\mathsf{cm}(S.\mathsf{mem}).
$$

**Register part / step descriptor.**
$\mathsf{RegPart} := \mathsf{Word}\to(\mathbb N\to\mathsf{Word})\to\mathsf{Word}\to(\mathbb N\to\mathsf{Word})\to\mathsf{Prop}$ (a relation on $(\mathsf{pc}_1,\mathsf{regs}_1,\mathsf{pc}_2,\mathsf{regs}_2)$).
The descriptor is the typed sum
$$
\mathsf{MemStep}(\mathsf{VC}) \;=\; \mathsf{read}(a{:}\mathsf{Index},\,v{:}\mathsf{Value},\,\pi{:}\mathsf{OpenProof})\ \mid\ \mathsf{write}(a,\,v,\,v_{\mathrm{old}},\,\pi)\ \mid\ \mathsf{other}.
$$

**Committed op predicates** (write $\varrho:=\mathrm{regPart}(\hat S_1.\mathsf{pc},\hat S_1.\mathsf{regs},\hat S_2.\mathsf{pc},\hat S_2.\mathsf{regs})$):
$$
\begin{aligned}
\widehat{\varphi}_{\mathrm{read}} &:\quad \varrho\ \wedge\ \hat S_1.\widehat{\mathsf{mem}}=\hat S_2.\widehat{\mathsf{mem}}\ \wedge\ \mathsf{Vf}(\hat S_1.\widehat{\mathsf{mem}},\,a,\,v,\,\pi),\\
\widehat{\varphi}_{\mathrm{write}} &:\quad \varrho\ \wedge\ \mathsf{Vf}(\hat S_1.\widehat{\mathsf{mem}},\,a,\,v_{\mathrm{old}},\,\pi)\ \wedge\ \mathsf{Vf}(\hat S_2.\widehat{\mathsf{mem}},\,a,\,v,\,\pi).
\end{aligned}
$$

**Full-memory op predicates** (write $\varrho:=\mathrm{regPart}(S_1.\mathsf{pc},S_1.\mathsf{regs},S_2.\mathsf{pc},S_2.\mathsf{regs})$):
$$
\begin{aligned}
\varphi_{\mathrm{read}} &:\quad \varrho\ \wedge\ S_1.\mathsf{mem}(a)=v\ \wedge\ S_2.\mathsf{mem}=S_1.\mathsf{mem},\\
\varphi_{\mathrm{write}} &:\quad \varrho\ \wedge\ S_2.\mathsf{mem}(a)=v\ \wedge\ \forall j\neq a,\ S_2.\mathsf{mem}(j)=S_1.\mathsf{mem}(j).
\end{aligned}
$$
(The point-wise write avoids requiring $\mathsf{DecidableEq}$ on $\mathsf{Index}$.)

**Classified steps** (dispatch on the descriptor $w$):
$$
\widehat{\varphi}_{\mathrm{step}}(\mathrm{regPart},\hat S_1,\hat S_2,w) = \begin{cases}\widehat{\varphi}_{\mathrm{read}} & w=\mathsf{read}\\ \widehat{\varphi}_{\mathrm{write}} & w=\mathsf{write}\\ \varrho\wedge \hat S_1.\widehat{\mathsf{mem}}=\hat S_2.\widehat{\mathsf{mem}} & w=\mathsf{other}\end{cases}
$$
and $\varphi_{\mathrm{step}}$ analogously with $\varphi_{\mathrm{read}}/\varphi_{\mathrm{write}}$ and, for $\mathsf{other}$, $\varrho\wedge S_2.\mathsf{mem}=S_1.\mathsf{mem}$.
(In Lean, $\widehat{\varphi}_{\mathrm{step}}=\mathsf{stepC}$, $\varphi_{\mathrm{step}}=\mathsf{stepF}$.)

### Lemma and theorem

**Injectivity of commitment on memories** (`mem_eq_of_commit_eq`).
$$
\mathsf{Complete}(\mathsf{VC})\ \wedge\ \mathsf{PB}(\mathsf{VC})\ \wedge\ \mathsf{cm}(m_1)=\mathsf{cm}(m_2)\quad\Rightarrow\quad m_2=m_1.
$$
*Proof.* Fix $i$. The honest opening gives $\mathsf{Vf}(\mathsf{cm}(m_1),i,m_2(i),\mathsf{op}(m_2,i))$ after rewriting by the hypothesis, and $\mathsf{Vf}(\mathsf{cm}(m_1),i,m_1(i),\mathsf{op}(m_1,i))$ directly; $\mathsf{PB}$ forces $m_1(i)=m_2(i)$; `funext`. $\square$

**Memory extractability, one step** (`step_mem_extract`) — *the core proposition*.
$$
\boxed{\ 
\begin{array}{c}
\mathsf{Complete}(\mathsf{VC})\ \wedge\ \mathsf{PB}(\mathsf{VC})\ \wedge\ \mathsf{PuB}(\mathsf{VC})\ \wedge\\[2pt]
\mathsf{CommitInv}(\hat S_1,S_1)\ \wedge\ \mathsf{CommitInv}(\hat S_2,S_2)\ \wedge\ \widehat{\varphi}_{\mathrm{step}}(\mathrm{regPart},\hat S_1,\hat S_2,w)\\[4pt]
\Longrightarrow\quad \varphi_{\mathrm{step}}(\mathrm{regPart},S_1,S_2,w)
\end{array}
\ }
$$
*Proof (case on $w$; mirrors the paper's Step A without probabilities).*
The register part transfers by rewriting $\mathsf{pc}/\mathsf{regs}$ through $\mathsf{CommitInv}$ in all cases.
- **$\mathsf{other}$:** memory equality $S_2.\mathsf{mem}=S_1.\mathsf{mem}$ from $\hat S_1.\widehat{\mathsf{mem}}=\hat S_2.\widehat{\mathsf{mem}}$, i.e. $\mathsf{cm}(S_1.\mathsf{mem})=\mathsf{cm}(S_2.\mathsf{mem})$, via `mem_eq_of_commit_eq`.
- **$\mathsf{read}(a,v,\pi)$:** For $S_1.\mathsf{mem}(a)=v$: the descriptor's $\pi$ verifies $\mathsf{cm}(S_1.\mathsf{mem})$ at $a$ to $v$ (rewrite $\hat S_1.\widehat{\mathsf{mem}}$), the honest opening verifies it to $S_1.\mathsf{mem}(a)$; $\mathsf{PB}$ equates them. For $S_2.\mathsf{mem}=S_1.\mathsf{mem}$: `mem_eq_of_commit_eq`.
- **$\mathsf{write}(a,v,v_{\mathrm{old}},\pi)$:** At $a$: $\pi$ verifies $\mathsf{cm}(S_2.\mathsf{mem})$ at $a$ to $v$ vs. the honest opening to $S_2.\mathsf{mem}(a)$; $\mathsf{PB}$ gives $S_2.\mathsf{mem}(a)=v$. Off $a$ ($j\neq a$): the *same* $\pi$ opens $\mathsf{cm}(S_1.\mathsf{mem})$ (to $v_{\mathrm{old}}$) and $\mathsf{cm}(S_2.\mathsf{mem})$ (to $v$) at $a$; $\mathsf{PuB}$ with the honest openings at $j$ forces $S_1.\mathsf{mem}(j)=S_2.\mathsf{mem}(j)$. $\square$

---

## 4. The two-step VM (`Twostep.lean`)

A concrete instance that keeps the two non-trivial features — extraction composed
across SNARK layers, and committed-memory states — and instantiates the abstract $V$.

### Definitions

**Statements / witnesses.**
$\mathsf{SegStmt}=(\mathsf{Sin},\mathsf{Sout}:\hat S)$;
$\mathsf{SegWitness}=(\mathsf{states}:\mathbb N\to\hat S,\ \mathsf{steps}:\mathbb N\to\mathsf{MemStep})$;
$\mathsf{FinalStmt}=(\mathsf{S0},\mathsf{ST}:\hat S)$;
$\mathsf{FinalWitness}=(\mathsf{boundary}:\mathbb N\to\hat S,\ \mathsf{proofs}:\mathbb N\to\mathsf{SegProof})$.

**System.** $\mathsf{sys}=(\mathsf{VC},\ N_{\mathrm{seg}},\ m,\ \mathrm{regPart}:\mathsf{RegPart},\ \mathsf{SegProof},\ \mathsf{segVerify},\ \mathsf{FinalProof},\ \mathsf{finalVerify})$.
Note the step is **not** an opaque field: it is the classified $\widehat{\varphi}_{\mathrm{step}}(\mathrm{regPart})$ from §3.

**Existential step projection** (bridges the descriptor-carrying step to the descriptor-free abstract $V$):
$$
\mathsf{stepRel}(\hat S_1,\hat S_2) \;:=\; \exists\, w:\mathsf{MemStep},\ \widehat{\varphi}_{\mathrm{step}}(\mathrm{regPart},\hat S_1,\hat S_2,w).
$$

**Segment relation.**
$$
R_{\mathrm{seg}}.\mathrm{rel}(st,w) := w.\mathsf{states}(0)=st.\mathsf{Sin}\ \wedge\ w.\mathsf{states}(N_{\mathrm{seg}})=st.\mathsf{Sout}\ \wedge\ \forall j<N_{\mathrm{seg}},\ \widehat{\varphi}_{\mathrm{step}}\bigl(\mathrm{regPart},\,w.\mathsf{states}(j),\,w.\mathsf{states}(j{+}1),\,w.\mathsf{steps}(j)\bigr).
$$

**Final relation.**
$$
R_{\mathrm{final}}.\mathrm{rel}(st,w) := w.\mathsf{boundary}(0)=st.\mathsf{S0}\ \wedge\ w.\mathsf{boundary}(m)=st.\mathsf{ST}\ \wedge\ \forall i<m,\ \mathsf{segVerify}\bigl(\langle w.\mathsf{boundary}(i),\,w.\mathsf{boundary}(i{+}1)\rangle,\ w.\mathsf{proofs}(i)\bigr).
$$
(The final relation asserts *segment proofs verify* — this is what forces recursive extractor composition.)

**Instantiation.** $\mathsf{toZkVM} := (\ \mathsf{State}=\hat S,\ \mathsf{step}=\mathsf{stepRel},\ T=m\cdot N_{\mathrm{seg}},\ \mathsf{Stmt}=\mathsf{FinalStmt},\ \mathsf{initial}=\mathsf{S0},\ \mathsf{terminal}=\mathsf{ST},\ \mathsf{Proof}=\mathsf{FinalProof},\ \mathsf{verify}=\mathsf{finalVerify}\ )$.

### Theorem

**CTE for the two-step VM** (`cte`).
$$
\boxed{\ 0<N_{\mathrm{seg}}\ \wedge\ \mathsf{KS}(\mathsf{AS}_{\mathrm{seg}})\ \wedge\ \mathsf{KS}(\mathsf{AS}_{\mathrm{final}})\ \Longrightarrow\ \mathsf{CTE}(\mathsf{toZkVM})\ }
$$
*Proof.* By the keystone (§2) it suffices to show $\mathsf{KS}(\mathsf{AS}^\star)$. Two-layer straight-line extraction: from an accepting final proof, extract the $R_{\mathrm{final}}$ witness (boundaries $d$ and per-segment proofs); for each $i<m$ extract an $R_{\mathrm{seg}}$ witness from proof $i$, giving states $seg\,i\,\cdot$ and descriptors. Each segment obligation $\widehat{\varphi}_{\mathrm{step}}(\mathrm{regPart},seg\,i\,j,seg\,i\,(j{+}1),\mathsf{steps}\,j)$ is repackaged as $\mathsf{stepRel}(seg\,i\,j,seg\,i\,(j{+}1))$ by $\exists$-introduction on the extracted descriptor. `chain_flatten` (§2) then glues the $m$ committed sub-chains into one valid $m N_{\mathrm{seg}}$-step trace from $\mathsf{S0}$ to $\mathsf{ST}$. $\square$

---

## 5. Bus-delegated segment extraction (`Bus.lean`)

An independent instance modeling the leaf layer: four inner circuits sharing one bus commitment.

### Definitions

**System.** $\mathsf{sys}=(\mathsf{VC},\ H,\ N_{\mathrm{seg}},\ \mathsf{StepAux},\ \mathsf{stepBus},\ \mathsf{keccak},\ \mathsf{poseidon},\ \mathsf{range},\ \dots)$
with $\mathsf{stepBus}:\hat S\to\hat S\to H.\mathsf{Domain}\to\mathsf{StepAux}\to\mathsf{Prop}$ and the three chip predicates over $H.\mathsf{Domain}$, plus proof types/verifiers for the four inner systems and the segment system.

**Complete committed step.**
$$
\mathsf{step}(S_1,S_2,\mathrm{bus},\mathrm{aux}) := \mathsf{stepBus}(S_1,S_2,\mathrm{bus},\mathrm{aux})\ \wedge\ \mathsf{keccak}(\mathrm{bus})\ \wedge\ \mathsf{poseidon}(\mathrm{bus})\ \wedge\ \mathsf{range}(\mathrm{bus}).
$$

**Inner-step relation.**
$$
R_{0,\mathrm{step}}.\mathrm{rel}(st,w) := w.\mathsf{states}(0)=st.\mathsf{Sin}\ \wedge\ w.\mathsf{states}(N_{\mathrm{seg}})=st.\mathsf{Sout}\ \wedge\ \bigl(\forall j<N_{\mathrm{seg}},\ \mathsf{stepBus}(w.\mathsf{states}(j),w.\mathsf{states}(j{+}1),w.\mathsf{bus},w.\mathsf{stepAux}(j))\bigr)\ \wedge\ st.\mathsf{busCom}=H.\mathsf{hash}(w.\mathsf{bus}).
$$

**Chip relation.** $R_{0,\mathrm{chip}}(\mathrm{pred}).\mathrm{rel}(\mathrm{busCom},\mathrm{bus}) := \mathrm{pred}(\mathrm{bus})\ \wedge\ \mathrm{busCom}=H.\mathsf{hash}(\mathrm{bus})$, instantiated at $\mathsf{keccak},\mathsf{poseidon},\mathsf{range}$.

**Segment relation** (proof-carrying).
$$
R_1.\mathrm{rel}(st,w) := \mathsf{innerStepVerify}(\langle st.\mathsf{Sin},st.\mathsf{Sout},w.\mathsf{busCom}\rangle,w.\mathsf{stepProof})\ \wedge\ \mathsf{innerKeccakVerify}(w.\mathsf{busCom},\dots)\ \wedge\ (\text{poseidon})\ \wedge\ (\text{range}).
$$

**Semantic segment relation** (post-unification target).
$$
R_{\mathrm{seg\text{-}trace}}.\mathrm{rel}(st,w) := w.\mathsf{states}(0)=st.\mathsf{Sin}\ \wedge\ w.\mathsf{states}(N_{\mathrm{seg}})=st.\mathsf{Sout}\ \wedge\ \forall j<N_{\mathrm{seg}},\ \mathsf{step}(w.\mathsf{states}(j),w.\mathsf{states}(j{+}1),w.\mathsf{bus},w.\mathsf{stepAux}(j)).
$$

### Theorem

**Segment extraction** (`segment_extract`).
$$
\boxed{\ \mathsf{CR}(H)\ \wedge\ \mathsf{KS}(\mathsf{AS}_{0,\mathrm{step}})\ \wedge\ \mathsf{KS}(\mathsf{AS}_{0,\mathrm{keccak}})\ \wedge\ \mathsf{KS}(\mathsf{AS}_{0,\mathrm{poseidon}})\ \wedge\ \mathsf{KS}(\mathsf{AS}_{0,\mathrm{range}})\ \wedge\ \mathsf{KS}(\mathsf{AS}_1)\ \Longrightarrow\ \mathsf{KS}(\mathsf{AS}_{\mathrm{seg\text{-}trace}})\ }
$$
*Proof.* Extract the four inner proofs from $R_1$, then their witnesses (one bus each). All four extracted buses hash to the segment witness's $\mathsf{busCom}$; $\mathsf{CR}(H)$ makes them **equal** to the inner-step bus. Transport the three chip predicates onto that single bus; combine with $\mathsf{stepBus}$ to obtain the complete $\mathsf{step}$ at every $j<N_{\mathrm{seg}}$. $\square$

---

## 6. Summary: assumptions consumed vs. conclusions

| Theorem | Consumes | Concludes |
|---|---|---|
| `cte_iff_knowledgeSound` | — (structural) | $\mathsf{CTE}(V)\iff\mathsf{KS}(\mathsf{AS}^\star)$ |
| `chain_flatten` | $0<N_{\mathrm{seg}}$, per-segment validity | one valid $mN_{\mathrm{seg}}$-step trace |
| `mem_eq_of_commit_eq` | $\mathsf{Complete},\mathsf{PB}$ | commitment injective on memories |
| **`step_mem_extract`** | $\mathsf{Complete},\mathsf{PB},\mathsf{PuB}$, $\mathsf{CommitInv}$ | committed step $\Rightarrow$ full-memory step |
| `cte` (TwoStep) | $0<N_{\mathrm{seg}}$, $\mathsf{KS}(\mathsf{AS}_{\mathrm{seg}}),\mathsf{KS}(\mathsf{AS}_{\mathrm{final}})$ | $\mathsf{CTE}(\mathsf{toZkVM})$ |
| `segment_extract` (Bus) | $\mathsf{CR}(H)$, $\mathsf{KS}$ of 4 inner + segment | $\mathsf{KS}(\mathsf{AS}_{\mathrm{seg\text{-}trace}})$ |

**Axiom footprint.** `#print axioms` reports `step_mem_extract : [Quot.sound]` and
`cte : [propext, Quot.sound]` — standard Lean axioms only, no `sorryAx`, not even
`Classical.choice`. The development is complete relative to its stated hypotheses.

**What is assumed, not proven** (matching the whitepaper's idealizations):
knowledge-soundness of every argument system ($\mathsf{KS}(\cdots)$), the binding
and collision-resistance properties of the two commitments, and $\mathsf{Complete}$
are all *hypotheses*, discharged by no concrete scheme here. A concrete
`VectorCommitment`/`HashCommitment` instance deriving them is out of scope.

**What is not yet connected** (open increments):
1. **Full-memory trace fold.** `step_mem_extract` is a single-step lemma; the fold reconstructing $\mathsf{mem}_0\dots\mathsf{mem}_T$ and strengthening `cte`'s conclusion from committed states to real memory is Stage 3.2/3.3.
2. **Bus ↔ two-step link.** `Bus.lean`'s $\mathsf{stepBus}/\mathsf{StepAux}$ and `Memory.lean`'s $\mathrm{regPart}/\mathsf{MemStep}$ are parallel; unifying them is open.
3. **Recursion tree.** $R_{\mathrm{final}}$ is a flat $m$-way merge, not the whitepaper's `convert`/`combine`/`embed` tower.
