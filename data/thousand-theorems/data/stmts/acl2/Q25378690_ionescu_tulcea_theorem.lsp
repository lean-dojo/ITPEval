;; Statement-only formalization of thousand-theorems corpus artifact Q25378690,
;; "Ionescu-Tulcea theorem": arbitrary measurable state spaces and a family of
;; Markov transition kernels determine a Markov kernel on infinite trajectories
;; whose every finite-coordinate marginal is the iterated finite trajectory.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; All mathematical carriers, sets, functions, measures, and kernels below are
;; unrestricted ACL2 objects.  The predicates impose the full sigma-algebra,
;; countable-additivity, measurability, dependent-product, and finite-iteration
;; interfaces used by the source.  No carrier is enumerated or made finite.

(defstub q25378690-domain-member-p (domain object) t)
(defstub q25378690-set-member-p (set object) t)
(defstub q25378690-function-at (function argument) t)
(defstub q25378690-sequence-at (sequence index) t)
(defstub q25378690-measurable-set-p (sigma set) t)

(defstub q25378690-ennreal-member-p (ennreal value) t)
(defstub q25378690-ennreal-zero (ennreal) t)
(defstub q25378690-ennreal-one (ennreal) t)
(defstub q25378690-ennreal-add (ennreal left right) t)
(defstub q25378690-ennreal-multiply (ennreal left right) t)
(defstub q25378690-ennreal-leq (ennreal left right) t)

(defstub q25378690-empty-set (domain) t)
(defstub q25378690-full-set (domain) t)
(defstub q25378690-complement-set (domain set) t)
(defstub q25378690-countable-union-set (domain sequence) t)
(defstub q25378690-upper-preimage-set
  (ennreal domain function threshold) t)

(defstub q25378690-measure-value (measure set) t)
(defstub q25378690-lintegral-value
  (lintegral ennreal domain sigma measure function) t)

(defstub q25378690-state-domain (spaces index) t)
(defstub q25378690-state-sigma (spaces index) t)
(defstub q25378690-history-domain (spaces last-index) t)
(defstub q25378690-history-sigma (spaces last-index) t)
(defstub q25378690-trajectory-domain (spaces) t)
(defstub q25378690-trajectory-sigma (spaces) t)

(defstub q25378690-history-coordinate
  (spaces last-index history index) t)
(defstub q25378690-trajectory-coordinate
  (spaces trajectory index) t)
(defstub q25378690-history-restrict
  (spaces from-index to-index history) t)
(defstub q25378690-trajectory-restrict
  (spaces to-index trajectory) t)
(defstub q25378690-history-extend
  (spaces last-index history next-state) t)

(defstub q25378690-history-coordinate-cylinder
  (spaces last-index index state-set) t)
(defstub q25378690-trajectory-coordinate-cylinder
  (spaces index state-set) t)
(defstub q25378690-prefix-cylinder
  (spaces last-index history-set) t)
(defstub q25378690-step-section-set
  (spaces last-index history-set history) t)

(defstub q25378690-kernel-measure (kernel input) t)
(defstub q25378690-kernel-mass-function (kernel event) t)
(defstub q25378690-transition-kernel (transitions index) t)
(defstub q25378690-partial-kernel
  (spaces transitions start-index last-index) t)
(defstub q25378690-step-integrand
  (spaces transitions last-index history-set) t)
(defstub q25378690-step-measure
  (spaces transitions lintegral last-index history-measure) t)

;; Extended nonnegative real arithmetic, including countable sums as suprema
;; of finite partial sums.

(defun-sk q25378690-ennreal-order-laws-p (ennreal)
  (forall (x y z)
    (implies
     (and
      (q25378690-ennreal-member-p ennreal x)
      (q25378690-ennreal-member-p ennreal y)
      (q25378690-ennreal-member-p ennreal z))
     (and
      (q25378690-ennreal-leq ennreal x x)
      (implies
       (and
        (q25378690-ennreal-leq ennreal x y)
        (q25378690-ennreal-leq ennreal y x))
       (equal x y))
      (implies
       (and
        (q25378690-ennreal-leq ennreal x y)
        (q25378690-ennreal-leq ennreal y z))
       (q25378690-ennreal-leq ennreal x z))
      (or
       (q25378690-ennreal-leq ennreal x y)
       (q25378690-ennreal-leq ennreal y x))))))

(defun-sk q25378690-ennreal-operation-laws-p (ennreal)
  (forall (x y z)
    (implies
     (and
      (q25378690-ennreal-member-p ennreal x)
      (q25378690-ennreal-member-p ennreal y)
      (q25378690-ennreal-member-p ennreal z))
     (let ((zero (q25378690-ennreal-zero ennreal))
           (one (q25378690-ennreal-one ennreal)))
       (and
        (q25378690-ennreal-member-p
         ennreal (q25378690-ennreal-add ennreal x y))
        (q25378690-ennreal-member-p
         ennreal (q25378690-ennreal-multiply ennreal x y))
        (equal
         (q25378690-ennreal-add
          ennreal (q25378690-ennreal-add ennreal x y) z)
         (q25378690-ennreal-add
          ennreal x (q25378690-ennreal-add ennreal y z)))
        (equal
         (q25378690-ennreal-add ennreal x y)
         (q25378690-ennreal-add ennreal y x))
        (equal (q25378690-ennreal-add ennreal x zero) x)
        (equal
         (q25378690-ennreal-multiply
          ennreal (q25378690-ennreal-multiply ennreal x y) z)
         (q25378690-ennreal-multiply
          ennreal x (q25378690-ennreal-multiply ennreal y z)))
        (equal
         (q25378690-ennreal-multiply ennreal x y)
         (q25378690-ennreal-multiply ennreal y x))
        (equal (q25378690-ennreal-multiply ennreal x one) x)
        (equal (q25378690-ennreal-multiply ennreal x zero) zero)
        (equal
         (q25378690-ennreal-multiply
          ennreal x (q25378690-ennreal-add ennreal y z))
         (q25378690-ennreal-add
          ennreal
          (q25378690-ennreal-multiply ennreal x y)
          (q25378690-ennreal-multiply ennreal x z)))
        (q25378690-ennreal-leq ennreal zero x)
        (implies
         (q25378690-ennreal-leq ennreal x y)
         (q25378690-ennreal-leq
          ennreal
          (q25378690-ennreal-add ennreal x z)
          (q25378690-ennreal-add ennreal y z))))))))

(defun q25378690-ennreal-structure-p (ennreal)
  (and
   (q25378690-ennreal-member-p
    ennreal (q25378690-ennreal-zero ennreal))
   (q25378690-ennreal-member-p
    ennreal (q25378690-ennreal-one ennreal))
   (not
    (equal
     (q25378690-ennreal-zero ennreal)
     (q25378690-ennreal-one ennreal)))
   (q25378690-ennreal-order-laws-p ennreal)
   (q25378690-ennreal-operation-laws-p ennreal)))

(defun q25378690-value-prefix-sum
    (ennreal value-function count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q25378690-ennreal-zero ennreal)
    (q25378690-ennreal-add
     ennreal
     (q25378690-value-prefix-sum
      ennreal value-function (- count 1))
     (q25378690-function-at value-function (- count 1)))))

(defun-sk q25378690-prefix-sums-bounded-p
    (ennreal value-function bound)
  (forall (count)
    (implies
     (natp count)
     (q25378690-ennreal-leq
      ennreal
      (q25378690-value-prefix-sum
       ennreal value-function count)
      bound))))

(defun-sk q25378690-countable-sum-p
    (ennreal value-function total)
  (forall (bound)
    (and
     (q25378690-ennreal-member-p ennreal total)
     (q25378690-prefix-sums-bounded-p
      ennreal value-function total)
     (implies
      (and
       (q25378690-ennreal-member-p ennreal bound)
       (q25378690-prefix-sums-bounded-p
        ennreal value-function bound))
      (q25378690-ennreal-leq ennreal total bound)))))

;; Arbitrary sets and sigma algebras.

(defun-sk q25378690-valid-set-p (domain set)
  (forall (x)
    (implies
     (q25378690-set-member-p set x)
     (q25378690-domain-member-p domain x))))

(defun-sk q25378690-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q25378690-domain-member-p domain x)
     (iff
      (q25378690-set-member-p left x)
      (q25378690-set-member-p right x)))))

(defun-sk q25378690-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q25378690-valid-set-p
      domain (q25378690-sequence-at sequence n)))))

(defun-sk q25378690-measurable-sequence-p (sigma sequence)
  (forall (n)
    (implies
     (natp n)
     (q25378690-measurable-set-p
      sigma (q25378690-sequence-at sequence n)))))

(defun-sk q25378690-pairwise-disjoint-p (sequence)
  (forall (m n x)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (not
      (and
       (q25378690-set-member-p
        (q25378690-sequence-at sequence m) x)
       (q25378690-set-member-p
        (q25378690-sequence-at sequence n) x))))))

(defun-sk q25378690-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q25378690-set-member-p
      (q25378690-sequence-at sequence n) x))))

(defun-sk q25378690-basic-set-constructor-laws-p (domain)
  (forall (set sequence x)
    (and
     (iff
      (q25378690-set-member-p
       (q25378690-empty-set domain) x)
      nil)
     (iff
      (q25378690-set-member-p
       (q25378690-full-set domain) x)
      (q25378690-domain-member-p domain x))
     (implies
      (q25378690-valid-set-p domain set)
      (iff
       (q25378690-set-member-p
        (q25378690-complement-set domain set) x)
       (and
        (q25378690-domain-member-p domain x)
        (not (q25378690-set-member-p set x)))))
     (implies
      (q25378690-set-sequence-p domain sequence)
      (iff
       (q25378690-set-member-p
        (q25378690-countable-union-set domain sequence) x)
       (and
        (q25378690-domain-member-p domain x)
        (q25378690-sequence-union-member-p sequence x)))))))

(defun-sk q25378690-sigma-extensional-p (domain sigma)
  (forall (left right)
    (implies
     (q25378690-set-equiv-p domain left right)
     (iff
      (q25378690-measurable-set-p sigma left)
      (q25378690-measurable-set-p sigma right)))))

(defun-sk q25378690-sigma-members-valid-p (domain sigma)
  (forall (set)
    (implies
     (q25378690-measurable-set-p sigma set)
     (q25378690-valid-set-p domain set))))

(defun-sk q25378690-sigma-complements-p (domain sigma)
  (forall (set)
    (implies
     (q25378690-measurable-set-p sigma set)
     (q25378690-measurable-set-p
      sigma (q25378690-complement-set domain set)))))

(defun-sk q25378690-sigma-countable-unions-p (domain sigma)
  (forall (sequence)
    (implies
     (and
      (q25378690-set-sequence-p domain sequence)
      (q25378690-measurable-sequence-p sigma sequence))
     (q25378690-measurable-set-p
      sigma
      (q25378690-countable-union-set domain sequence)))))

(defun q25378690-sigma-algebra-p (domain sigma)
  (and
   (q25378690-basic-set-constructor-laws-p domain)
   (q25378690-sigma-extensional-p domain sigma)
   (q25378690-sigma-members-valid-p domain sigma)
   (q25378690-measurable-set-p
    sigma (q25378690-empty-set domain))
   (q25378690-sigma-complements-p domain sigma)
   (q25378690-sigma-countable-unions-p domain sigma)))

;; Countably additive probability measures.

(defstub q25378690-measure-sequence-values
  (measure sequence) t)

(defun-sk q25378690-measure-sequence-values-laws-p ()
  (forall (measure sequence n)
    (implies
     (natp n)
     (equal
      (q25378690-function-at
       (q25378690-measure-sequence-values measure sequence) n)
      (q25378690-measure-value
       measure (q25378690-sequence-at sequence n))))))

(defun-sk q25378690-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q25378690-set-equiv-p domain left right)
     (equal
      (q25378690-measure-value measure left)
      (q25378690-measure-value measure right)))))

(defun-sk q25378690-measure-values-p
    (ennreal sigma measure)
  (forall (set)
    (implies
     (q25378690-measurable-set-p sigma set)
     (q25378690-ennreal-member-p
      ennreal (q25378690-measure-value measure set)))))

(defun-sk q25378690-countably-additive-p
    (ennreal domain sigma measure)
  (forall (sequence)
    (implies
     (and
      (q25378690-set-sequence-p domain sequence)
      (q25378690-measurable-sequence-p sigma sequence)
      (q25378690-pairwise-disjoint-p sequence))
     (q25378690-countable-sum-p
      ennreal
      (q25378690-measure-sequence-values measure sequence)
      (q25378690-measure-value
       measure
       (q25378690-countable-union-set domain sequence))))))

(defun q25378690-probability-measure-p
    (ennreal domain sigma measure)
  (and
   (q25378690-sigma-algebra-p domain sigma)
   (q25378690-measure-extensional-p domain measure)
   (q25378690-measure-values-p ennreal sigma measure)
   (equal
    (q25378690-measure-value
     measure (q25378690-empty-set domain))
    (q25378690-ennreal-zero ennreal))
   (q25378690-countably-additive-p
    ennreal domain sigma measure)
   (equal
    (q25378690-measure-value
     measure (q25378690-full-set domain))
    (q25378690-ennreal-one ennreal))))

;; Measurable ENNReal-valued functions and a lower-Lebesgue-integral interface.

(defun-sk q25378690-ennreal-function-p
    (ennreal domain function)
  (forall (x)
    (implies
     (q25378690-domain-member-p domain x)
     (q25378690-ennreal-member-p
      ennreal (q25378690-function-at function x)))))

(defun-sk q25378690-upper-preimage-laws-p
    (ennreal domain)
  (forall (function threshold x)
    (iff
     (q25378690-set-member-p
      (q25378690-upper-preimage-set
       ennreal domain function threshold)
      x)
     (and
      (q25378690-domain-member-p domain x)
      (not
       (q25378690-ennreal-leq
        ennreal
        (q25378690-function-at function x)
        threshold))))))

(defun-sk q25378690-measurable-ennreal-function-p
    (ennreal domain sigma function)
  (forall (threshold)
    (and
     (q25378690-ennreal-function-p ennreal domain function)
     (implies
      (q25378690-ennreal-member-p ennreal threshold)
      (q25378690-measurable-set-p
       sigma
       (q25378690-upper-preimage-set
        ennreal domain function threshold))))))

(defun-sk q25378690-lintegral-values-p
    (lintegral ennreal domain sigma measure)
  (forall (function)
    (implies
     (q25378690-measurable-ennreal-function-p
      ennreal domain sigma function)
     (q25378690-ennreal-member-p
      ennreal
      (q25378690-lintegral-value
       lintegral ennreal domain sigma measure function)))))

(defun-sk q25378690-functions-pointwise-leq-p
    (ennreal domain left right)
  (forall (x)
    (implies
     (q25378690-domain-member-p domain x)
     (q25378690-ennreal-leq
      ennreal
      (q25378690-function-at left x)
      (q25378690-function-at right x)))))

(defun-sk q25378690-lintegral-monotone-p
    (lintegral ennreal domain sigma measure)
  (forall (left right)
    (implies
     (and
      (q25378690-measurable-ennreal-function-p
       ennreal domain sigma left)
      (q25378690-measurable-ennreal-function-p
       ennreal domain sigma right)
      (q25378690-functions-pointwise-leq-p
       ennreal domain left right))
     (q25378690-ennreal-leq
      ennreal
      (q25378690-lintegral-value
       lintegral ennreal domain sigma measure left)
      (q25378690-lintegral-value
       lintegral ennreal domain sigma measure right)))))

(defun q25378690-lintegral-operation-p
    (lintegral ennreal domain sigma measure)
  (and
   (q25378690-upper-preimage-laws-p ennreal domain)
   (q25378690-lintegral-values-p
    lintegral ennreal domain sigma measure)
   (q25378690-lintegral-monotone-p
    lintegral ennreal domain sigma measure)))

;; Markov kernels: every input gives a probability measure and every measurable
;; event has a measurable mass function.

(defun-sk q25378690-kernel-mass-function-laws-p
    (kernel)
  (forall (event input)
    (equal
     (q25378690-function-at
      (q25378690-kernel-mass-function kernel event)
      input)
     (q25378690-measure-value
      (q25378690-kernel-measure kernel input)
      event))))

(defun-sk q25378690-kernel-probability-values-p
    (ennreal input-domain output-domain output-sigma kernel)
  (forall (input)
    (implies
     (q25378690-domain-member-p input-domain input)
     (q25378690-probability-measure-p
      ennreal output-domain output-sigma
      (q25378690-kernel-measure kernel input)))))

(defun-sk q25378690-kernel-sections-measurable-p
    (ennreal input-domain input-sigma output-sigma kernel)
  (forall (event)
    (implies
     (q25378690-measurable-set-p output-sigma event)
     (q25378690-measurable-ennreal-function-p
      ennreal input-domain input-sigma
      (q25378690-kernel-mass-function kernel event)))))

(defun q25378690-markov-kernel-p
    (ennreal input-domain input-sigma
     output-domain output-sigma kernel)
  (and
   (q25378690-sigma-algebra-p input-domain input-sigma)
   (q25378690-sigma-algebra-p output-domain output-sigma)
   (q25378690-kernel-mass-function-laws-p kernel)
   (q25378690-kernel-probability-values-p
    ennreal input-domain output-domain output-sigma kernel)
   (q25378690-kernel-sections-measurable-p
    ennreal input-domain input-sigma output-sigma kernel)))

;; Dependent finite histories and infinite trajectories carry the exact product
;; sigma algebras generated by coordinate cylinders.

(defun-sk q25378690-history-coordinate-typing-p
    (spaces last-index)
  (forall (history index)
    (implies
     (and
      (q25378690-domain-member-p
       (q25378690-history-domain spaces last-index) history)
      (natp index)
      (<= index last-index))
     (q25378690-domain-member-p
      (q25378690-state-domain spaces index)
      (q25378690-history-coordinate
       spaces last-index history index)))))

(defun-sk q25378690-trajectory-coordinate-typing-p (spaces)
  (forall (trajectory index)
    (implies
     (and
      (q25378690-domain-member-p
       (q25378690-trajectory-domain spaces) trajectory)
      (natp index))
     (q25378690-domain-member-p
      (q25378690-state-domain spaces index)
      (q25378690-trajectory-coordinate
       spaces trajectory index)))))

(defun-sk q25378690-history-coordinate-equal-p
    (spaces last-index left right)
  (forall (index)
    (implies
     (and (natp index) (<= index last-index))
     (equal
      (q25378690-history-coordinate
       spaces last-index left index)
      (q25378690-history-coordinate
       spaces last-index right index)))))

(defun-sk q25378690-trajectory-coordinate-equal-p
    (spaces left right)
  (forall (index)
    (implies
     (natp index)
     (equal
      (q25378690-trajectory-coordinate spaces left index)
      (q25378690-trajectory-coordinate spaces right index)))))

(defun-sk q25378690-path-extensionality-p (spaces)
  (forall (last-index left right trajectory-left trajectory-right)
    (and
     (implies
      (and
       (natp last-index)
       (q25378690-domain-member-p
        (q25378690-history-domain spaces last-index) left)
       (q25378690-domain-member-p
        (q25378690-history-domain spaces last-index) right)
       (q25378690-history-coordinate-equal-p
        spaces last-index left right))
      (equal left right))
     (implies
      (and
       (q25378690-domain-member-p
        (q25378690-trajectory-domain spaces) trajectory-left)
       (q25378690-domain-member-p
        (q25378690-trajectory-domain spaces) trajectory-right)
       (q25378690-trajectory-coordinate-equal-p
        spaces trajectory-left trajectory-right))
      (equal trajectory-left trajectory-right)))))

(defun-sk q25378690-history-function-typed-p
    (spaces last-index function)
  (forall (index)
    (implies
     (and (natp index) (<= index last-index))
     (q25378690-domain-member-p
      (q25378690-state-domain spaces index)
      (q25378690-function-at function index)))))

(defun-sk q25378690-trajectory-function-typed-p
    (spaces function)
  (forall (index)
    (implies
     (natp index)
     (q25378690-domain-member-p
      (q25378690-state-domain spaces index)
      (q25378690-function-at function index)))))

(defun-sk q25378690-history-realizer-agrees-p
    (spaces last-index function history)
  (forall (index)
    (implies
     (and (natp index) (<= index last-index))
     (equal
      (q25378690-history-coordinate
       spaces last-index history index)
      (q25378690-function-at function index)))))

(defun-sk q25378690-history-realizer-exists-p
    (spaces last-index function)
  (exists (history)
    (and
     (q25378690-domain-member-p
      (q25378690-history-domain spaces last-index) history)
     (q25378690-history-realizer-agrees-p
      spaces last-index function history))))

(defun-sk q25378690-trajectory-realizer-agrees-p
    (spaces function trajectory)
  (forall (index)
    (implies
     (natp index)
     (equal
      (q25378690-trajectory-coordinate
       spaces trajectory index)
      (q25378690-function-at function index)))))

(defun-sk q25378690-trajectory-realizer-exists-p
    (spaces function)
  (exists (trajectory)
    (and
     (q25378690-domain-member-p
      (q25378690-trajectory-domain spaces) trajectory)
     (q25378690-trajectory-realizer-agrees-p
      spaces function trajectory))))

(defun-sk q25378690-path-realization-p (spaces)
  (forall (last-index function)
    (and
     (implies
      (and
       (natp last-index)
       (q25378690-history-function-typed-p
        spaces last-index function))
      (q25378690-history-realizer-exists-p
       spaces last-index function))
     (implies
      (q25378690-trajectory-function-typed-p spaces function)
      (q25378690-trajectory-realizer-exists-p
       spaces function)))))

(defun-sk q25378690-restriction-laws-p (spaces)
  (forall (from-index to-index history trajectory index)
    (and
     (implies
      (and
       (natp from-index)
       (natp to-index)
       (<= to-index from-index)
       (q25378690-domain-member-p
        (q25378690-history-domain spaces from-index) history))
      (and
       (q25378690-domain-member-p
        (q25378690-history-domain spaces to-index)
        (q25378690-history-restrict
         spaces from-index to-index history))
       (implies
        (and (natp index) (<= index to-index))
        (equal
         (q25378690-history-coordinate
          spaces to-index
          (q25378690-history-restrict
           spaces from-index to-index history)
          index)
         (q25378690-history-coordinate
          spaces from-index history index)))))
     (implies
      (and
       (natp to-index)
       (q25378690-domain-member-p
        (q25378690-trajectory-domain spaces) trajectory))
      (and
       (q25378690-domain-member-p
        (q25378690-history-domain spaces to-index)
        (q25378690-trajectory-restrict
         spaces to-index trajectory))
       (implies
        (and (natp index) (<= index to-index))
        (equal
         (q25378690-history-coordinate
          spaces to-index
          (q25378690-trajectory-restrict
           spaces to-index trajectory)
          index)
         (q25378690-trajectory-coordinate
          spaces trajectory index))))))))

(defun-sk q25378690-extension-laws-p (spaces)
  (forall (last-index history next-state index)
    (implies
     (and
      (natp last-index)
      (q25378690-domain-member-p
       (q25378690-history-domain spaces last-index) history)
      (q25378690-domain-member-p
       (q25378690-state-domain spaces (+ 1 last-index))
       next-state))
     (and
      (q25378690-domain-member-p
       (q25378690-history-domain spaces (+ 1 last-index))
       (q25378690-history-extend
        spaces last-index history next-state))
      (implies
       (and (natp index) (<= index last-index))
       (equal
        (q25378690-history-coordinate
         spaces (+ 1 last-index)
         (q25378690-history-extend
          spaces last-index history next-state)
         index)
        (q25378690-history-coordinate
         spaces last-index history index)))
      (equal
       (q25378690-history-coordinate
        spaces (+ 1 last-index)
        (q25378690-history-extend
         spaces last-index history next-state)
        (+ 1 last-index))
       next-state)))))

(defun-sk q25378690-history-cylinder-laws-p
    (spaces last-index)
  (forall (index state-set history)
    (implies
     (and
      (natp index)
      (<= index last-index)
      (q25378690-measurable-set-p
       (q25378690-state-sigma spaces index) state-set))
     (and
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces last-index)
       (q25378690-history-coordinate-cylinder
        spaces last-index index state-set))
      (iff
       (q25378690-set-member-p
        (q25378690-history-coordinate-cylinder
         spaces last-index index state-set)
        history)
       (and
        (q25378690-domain-member-p
         (q25378690-history-domain spaces last-index) history)
        (q25378690-set-member-p
         state-set
         (q25378690-history-coordinate
          spaces last-index history index))))))))

(defun-sk q25378690-trajectory-cylinder-laws-p (spaces)
  (forall (index state-set trajectory)
    (implies
     (and
      (natp index)
      (q25378690-measurable-set-p
       (q25378690-state-sigma spaces index) state-set))
     (and
      (q25378690-measurable-set-p
       (q25378690-trajectory-sigma spaces)
       (q25378690-trajectory-coordinate-cylinder
        spaces index state-set))
      (iff
       (q25378690-set-member-p
        (q25378690-trajectory-coordinate-cylinder
         spaces index state-set)
        trajectory)
       (and
        (q25378690-domain-member-p
         (q25378690-trajectory-domain spaces) trajectory)
        (q25378690-set-member-p
         state-set
         (q25378690-trajectory-coordinate
          spaces trajectory index))))))))

(defun-sk q25378690-history-cylinders-in-sigma-p
    (spaces last-index sigma)
  (forall (index state-set)
    (implies
     (and
      (natp index)
      (<= index last-index)
      (q25378690-measurable-set-p
       (q25378690-state-sigma spaces index) state-set))
     (q25378690-measurable-set-p
      sigma
      (q25378690-history-coordinate-cylinder
       spaces last-index index state-set)))))

(defun-sk q25378690-trajectory-cylinders-in-sigma-p
    (spaces sigma)
  (forall (index state-set)
    (implies
     (and
      (natp index)
      (q25378690-measurable-set-p
       (q25378690-state-sigma spaces index) state-set))
     (q25378690-measurable-set-p
      sigma
      (q25378690-trajectory-coordinate-cylinder
       spaces index state-set)))))

(defun-sk q25378690-history-product-minimal-p
    (spaces last-index)
  (forall (sigma set)
    (implies
     (and
      (q25378690-sigma-algebra-p
       (q25378690-history-domain spaces last-index) sigma)
      (q25378690-history-cylinders-in-sigma-p
       spaces last-index sigma)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces last-index) set))
     (q25378690-measurable-set-p sigma set))))

(defun-sk q25378690-trajectory-product-minimal-p (spaces)
  (forall (sigma set)
    (implies
     (and
      (q25378690-sigma-algebra-p
       (q25378690-trajectory-domain spaces) sigma)
      (q25378690-trajectory-cylinders-in-sigma-p spaces sigma)
      (q25378690-measurable-set-p
       (q25378690-trajectory-sigma spaces) set))
     (q25378690-measurable-set-p sigma set))))

(defun-sk q25378690-prefix-cylinder-laws-p (spaces)
  (forall (last-index history-set trajectory)
    (implies
     (and
      (natp last-index)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces last-index)
       history-set))
     (and
      (q25378690-measurable-set-p
       (q25378690-trajectory-sigma spaces)
       (q25378690-prefix-cylinder
        spaces last-index history-set))
      (iff
       (q25378690-set-member-p
        (q25378690-prefix-cylinder
         spaces last-index history-set)
        trajectory)
       (and
        (q25378690-domain-member-p
         (q25378690-trajectory-domain spaces) trajectory)
        (q25378690-set-member-p
         history-set
         (q25378690-trajectory-restrict
          spaces last-index trajectory))))))))

(defun-sk q25378690-state-space-family-p (spaces)
  (forall (index)
    (implies
     (natp index)
     (q25378690-sigma-algebra-p
      (q25378690-state-domain spaces index)
      (q25378690-state-sigma spaces index)))))

(defun-sk q25378690-dependent-product-family-p (spaces)
  (forall (last-index)
    (implies
     (natp last-index)
     (and
      (q25378690-sigma-algebra-p
       (q25378690-history-domain spaces last-index)
       (q25378690-history-sigma spaces last-index))
      (q25378690-history-coordinate-typing-p
       spaces last-index)
      (q25378690-history-cylinder-laws-p
       spaces last-index)
      (q25378690-history-product-minimal-p
       spaces last-index)))))

(defun q25378690-path-space-interface-p (spaces)
  (and
   (q25378690-state-space-family-p spaces)
   (q25378690-dependent-product-family-p spaces)
   (q25378690-sigma-algebra-p
    (q25378690-trajectory-domain spaces)
    (q25378690-trajectory-sigma spaces))
   (q25378690-trajectory-coordinate-typing-p spaces)
   (q25378690-trajectory-cylinder-laws-p spaces)
   (q25378690-trajectory-product-minimal-p spaces)
   (q25378690-path-extensionality-p spaces)
   (q25378690-path-realization-p spaces)
   (q25378690-restriction-laws-p spaces)
   (q25378690-extension-laws-p spaces)
   (q25378690-prefix-cylinder-laws-p spaces)))

;; The source family κ n consists of Markov kernels from histories through n
;; to the next state X(n+1).

(defun-sk q25378690-transition-family-p
    (ennreal spaces transitions)
  (forall (index)
    (implies
     (natp index)
     (q25378690-markov-kernel-p
      ennreal
      (q25378690-history-domain spaces index)
      (q25378690-history-sigma spaces index)
      (q25378690-state-domain spaces (+ 1 index))
      (q25378690-state-sigma spaces (+ 1 index))
      (q25378690-transition-kernel transitions index)))))

;; A one-step composition product keeps the existing finite history and samples
;; its next coordinate from κ.  The section and integrand equations below are
;; the standard semidirect-product measure formula.

(defun-sk q25378690-step-section-laws-p (spaces)
  (forall (last-index history-set history next-state)
    (implies
     (and
      (natp last-index)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces (+ 1 last-index))
       history-set)
      (q25378690-domain-member-p
       (q25378690-history-domain spaces last-index)
       history))
     (and
      (q25378690-measurable-set-p
       (q25378690-state-sigma spaces (+ 1 last-index))
       (q25378690-step-section-set
        spaces last-index history-set history))
      (iff
       (q25378690-set-member-p
        (q25378690-step-section-set
         spaces last-index history-set history)
        next-state)
       (and
        (q25378690-domain-member-p
         (q25378690-state-domain spaces (+ 1 last-index))
         next-state)
        (q25378690-set-member-p
         history-set
         (q25378690-history-extend
          spaces last-index history next-state))))))))

(defun-sk q25378690-step-integrand-laws-p
    (ennreal spaces transitions)
  (forall (last-index history-set history)
    (implies
     (and
      (natp last-index)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces (+ 1 last-index))
       history-set)
      (q25378690-domain-member-p
       (q25378690-history-domain spaces last-index)
       history))
     (equal
      (q25378690-function-at
       (q25378690-step-integrand
        spaces transitions last-index history-set)
       history)
      (q25378690-measure-value
       (q25378690-kernel-measure
        (q25378690-transition-kernel
         transitions last-index)
        history)
       (q25378690-step-section-set
        spaces last-index history-set history))))))

(defun-sk q25378690-step-integrands-measurable-p
    (ennreal spaces transitions)
  (forall (last-index history-set)
    (implies
     (and
      (natp last-index)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces (+ 1 last-index))
       history-set))
     (q25378690-measurable-ennreal-function-p
      ennreal
      (q25378690-history-domain spaces last-index)
      (q25378690-history-sigma spaces last-index)
      (q25378690-step-integrand
       spaces transitions last-index history-set)))))

(defun-sk q25378690-step-measure-values-p
    (ennreal spaces transitions lintegral)
  (forall (last-index history-measure history-set)
    (implies
     (and
      (natp last-index)
      (q25378690-probability-measure-p
       ennreal
       (q25378690-history-domain spaces last-index)
       (q25378690-history-sigma spaces last-index)
       history-measure)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces (+ 1 last-index))
       history-set))
     (equal
      (q25378690-measure-value
       (q25378690-step-measure
        spaces transitions lintegral last-index history-measure)
       history-set)
      (q25378690-lintegral-value
       lintegral
       ennreal
       (q25378690-history-domain spaces last-index)
       (q25378690-history-sigma spaces last-index)
       history-measure
       (q25378690-step-integrand
        spaces transitions last-index history-set))))))

(defun-sk q25378690-step-measures-probability-p
    (ennreal spaces transitions lintegral)
  (forall (last-index history-measure)
    (implies
     (and
      (natp last-index)
      (q25378690-probability-measure-p
       ennreal
       (q25378690-history-domain spaces last-index)
       (q25378690-history-sigma spaces last-index)
       history-measure))
     (q25378690-probability-measure-p
      ennreal
      (q25378690-history-domain spaces (+ 1 last-index))
      (q25378690-history-sigma spaces (+ 1 last-index))
      (q25378690-step-measure
       spaces transitions lintegral
       last-index history-measure)))))

(defun-sk q25378690-all-history-lintegrals-p
    (lintegral ennreal spaces)
  (forall (last-index measure)
    (implies
     (and
      (natp last-index)
      (q25378690-probability-measure-p
       ennreal
       (q25378690-history-domain spaces last-index)
       (q25378690-history-sigma spaces last-index)
       measure))
     (q25378690-lintegral-operation-p
      lintegral ennreal
      (q25378690-history-domain spaces last-index)
      (q25378690-history-sigma spaces last-index)
      measure))))

;; The imported finite `partialTraj` construction is represented definitionally:
;; below the starting index it is deterministic restriction; each later level
;; is obtained by the preceding one-step composition product.

(defun-sk q25378690-partial-kernels-markov-p
    (ennreal spaces transitions)
  (forall (start-index last-index)
    (implies
     (and (natp start-index) (natp last-index))
     (q25378690-markov-kernel-p
      ennreal
      (q25378690-history-domain spaces start-index)
      (q25378690-history-sigma spaces start-index)
      (q25378690-history-domain spaces last-index)
      (q25378690-history-sigma spaces last-index)
      (q25378690-partial-kernel
       spaces transitions start-index last-index)))))

(defun-sk q25378690-partial-base-values-p
    (ennreal spaces transitions)
  (forall (start-index last-index input history-set)
    (implies
     (and
      (natp start-index)
      (natp last-index)
      (<= last-index start-index)
      (q25378690-domain-member-p
       (q25378690-history-domain spaces start-index) input)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces last-index)
       history-set))
     (equal
      (q25378690-measure-value
       (q25378690-kernel-measure
        (q25378690-partial-kernel
         spaces transitions start-index last-index)
        input)
       history-set)
      (if
       (q25378690-set-member-p
        history-set
        (q25378690-history-restrict
         spaces start-index last-index input))
       (q25378690-ennreal-one ennreal)
       (q25378690-ennreal-zero ennreal))))))

(defun-sk q25378690-measure-equal-p
    (sigma left right)
  (forall (set)
    (implies
     (q25378690-measurable-set-p sigma set)
     (equal
      (q25378690-measure-value left set)
      (q25378690-measure-value right set)))))

(defun-sk q25378690-partial-successor-values-p
    (spaces transitions lintegral)
  (forall (start-index last-index input)
    (implies
     (and
      (natp start-index)
      (natp last-index)
      (<= start-index last-index)
      (q25378690-domain-member-p
       (q25378690-history-domain spaces start-index) input))
     (q25378690-measure-equal-p
      (q25378690-history-sigma spaces (+ 1 last-index))
      (q25378690-kernel-measure
       (q25378690-partial-kernel
        spaces transitions start-index (+ 1 last-index))
       input)
      (q25378690-step-measure
       spaces transitions lintegral last-index
       (q25378690-kernel-measure
        (q25378690-partial-kernel
         spaces transitions start-index last-index)
        input))))))

(defun q25378690-finite-trajectory-interface-p
    (ennreal spaces transitions lintegral)
  (and
   (q25378690-step-section-laws-p spaces)
   (q25378690-step-integrand-laws-p
    ennreal spaces transitions)
   (q25378690-step-integrands-measurable-p
    ennreal spaces transitions)
   (q25378690-step-measure-values-p
    ennreal spaces transitions lintegral)
   (q25378690-step-measures-probability-p
    ennreal spaces transitions lintegral)
   (q25378690-all-history-lintegrals-p
    lintegral ennreal spaces)
   (q25378690-partial-kernels-markov-p
    ennreal spaces transitions)
   (q25378690-partial-base-values-p
    ennreal spaces transitions)
   (q25378690-partial-successor-values-p
    spaces transitions lintegral)))

;; Equality of every finite pushforward is stated on all measurable sets.

(defun-sk q25378690-all-finite-marginals-p
    (spaces transitions start-index trajectory-kernel)
  (forall (last-index input history-set)
    (implies
     (and
      (natp last-index)
      (q25378690-domain-member-p
       (q25378690-history-domain spaces start-index) input)
      (q25378690-measurable-set-p
       (q25378690-history-sigma spaces last-index)
       history-set))
     (equal
      (q25378690-measure-value
       (q25378690-kernel-measure trajectory-kernel input)
       (q25378690-prefix-cylinder
        spaces last-index history-set))
      (q25378690-measure-value
       (q25378690-kernel-measure
        (q25378690-partial-kernel
         spaces transitions start-index last-index)
        input)
       history-set)))))

(defun q25378690-trajectory-kernel-p
    (ennreal spaces transitions start-index trajectory-kernel)
  (and
   (q25378690-markov-kernel-p
    ennreal
    (q25378690-history-domain spaces start-index)
    (q25378690-history-sigma spaces start-index)
    (q25378690-trajectory-domain spaces)
    (q25378690-trajectory-sigma spaces)
    trajectory-kernel)
   (q25378690-all-finite-marginals-p
    spaces transitions start-index trajectory-kernel)))

(defun-sk q25378690-trajectory-kernel-exists-p
    (ennreal spaces transitions start-index)
  (exists (trajectory-kernel)
    (q25378690-trajectory-kernel-p
     ennreal spaces transitions start-index trajectory-kernel)))

(defun-sk thousand-theorems-q25378690-ionescu-tulcea-theorem-statement ()
  (forall (ennreal spaces transitions lintegral start-index)
    (implies
     (and
      (natp start-index)
      (q25378690-ennreal-structure-p ennreal)
      (q25378690-measure-sequence-values-laws-p)
      (q25378690-path-space-interface-p spaces)
      (q25378690-transition-family-p
       ennreal spaces transitions)
      (q25378690-finite-trajectory-interface-p
       ennreal spaces transitions lintegral))
     (q25378690-trajectory-kernel-exists-p
      ennreal spaces transitions start-index))))

(value-triple :itpeval-statement-checked)
:q
