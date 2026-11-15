;; Statement-only formalization of thousand-theorems corpus artifact Q3527217,
;; "M. Riesz extension theorem": a real-linear functional on a subspace that
;; is nonnegative on its intersection with a pointed cone extends to the whole
;; vector space as a linear functional nonnegative on that cone, provided the
;; subspace plus the cone covers the space. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A context tag presents an arbitrary real vector space. A
;; Dedekind-complete ordered field presents the real scalars up to their unique
;; ordered-field isomorphism. Cone, subspace, partial-functional, and extension
;; tags are interpreted by conservative generic symbols; no carrier, set, or
;; function is replaced by a finite table. Every algebraic, order, typing,
;; closure, linearity, and theorem hypothesis is explicit below.

;; The complete linearly ordered real field.

(defstub q3527217-real-member-p (ctx value) t)
(defstub q3527217-real-zero (ctx) t)
(defstub q3527217-real-one (ctx) t)
(defstub q3527217-real-add (ctx left right) t)
(defstub q3527217-real-multiply (ctx left right) t)
(defstub q3527217-real-negate (ctx value) t)
(defstub q3527217-real-inverse (ctx value) t)
(defstub q3527217-real-less (ctx left right) t)
(defstub q3527217-real-set-member-p (ctx set-tag value) t)

(defun q3527217-real-leq (ctx left right)
  (not (q3527217-real-less ctx right left)))

(defun-sk q3527217-real-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q3527217-real-member-p ctx x)
      (q3527217-real-member-p ctx y)
      (q3527217-real-member-p ctx z))
     (let* ((zero (q3527217-real-zero ctx))
            (one (q3527217-real-one ctx))
            (xy-add (q3527217-real-add ctx x y))
            (yz-add (q3527217-real-add ctx y z))
            (xy-mul (q3527217-real-multiply ctx x y))
            (yz-mul (q3527217-real-multiply ctx y z))
            (neg-x (q3527217-real-negate ctx x))
            (inv-x (q3527217-real-inverse ctx x)))
       (and
        (q3527217-real-member-p ctx xy-add)
        (q3527217-real-member-p ctx xy-mul)
        (q3527217-real-member-p ctx neg-x)
        (q3527217-real-member-p ctx inv-x)
        (equal
         (q3527217-real-add ctx xy-add z)
         (q3527217-real-add ctx x yz-add))
        (equal xy-add (q3527217-real-add ctx y x))
        (equal (q3527217-real-add ctx x zero) x)
        (equal (q3527217-real-add ctx x neg-x) zero)
        (equal
         (q3527217-real-multiply ctx xy-mul z)
         (q3527217-real-multiply ctx x yz-mul))
        (equal
         xy-mul
         (q3527217-real-multiply ctx y x))
        (equal
         (q3527217-real-multiply ctx x one)
         x)
        (equal
         (q3527217-real-inverse ctx zero)
         zero)
        (implies
         (not (equal x zero))
         (equal
          (q3527217-real-multiply ctx x inv-x)
          one))
        (equal
         (q3527217-real-multiply
          ctx x (q3527217-real-add ctx y z))
         (q3527217-real-add
          ctx
          (q3527217-real-multiply ctx x y)
          (q3527217-real-multiply ctx x z))))))))

(defun-sk q3527217-real-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q3527217-real-member-p ctx x)
      (q3527217-real-member-p ctx y)
      (q3527217-real-member-p ctx z))
     (let ((zero (q3527217-real-zero ctx)))
       (and
        (not (q3527217-real-less ctx x x))
        (or
         (equal x y)
         (q3527217-real-less ctx x y)
         (q3527217-real-less ctx y x))
        (implies
         (and
          (q3527217-real-less ctx x y)
          (q3527217-real-less ctx y z))
         (q3527217-real-less ctx x z))
        (implies
         (q3527217-real-less ctx x y)
         (q3527217-real-less
          ctx
          (q3527217-real-add ctx x z)
          (q3527217-real-add ctx y z)))
        (implies
         (and
          (q3527217-real-less ctx zero x)
          (q3527217-real-less ctx zero y))
         (q3527217-real-less
          ctx
          zero
          (q3527217-real-multiply ctx x y))))))))

(defun-sk q3527217-valid-real-set-p (ctx set-tag)
  (forall (x)
    (implies
     (q3527217-real-set-member-p ctx set-tag x)
     (q3527217-real-member-p ctx x))))

(defun-sk q3527217-real-set-nonempty-p (ctx set-tag)
  (exists (x)
    (and
     (q3527217-real-member-p ctx x)
     (q3527217-real-set-member-p ctx set-tag x))))

(defun-sk q3527217-real-upper-bound-p
    (ctx set-tag bound)
  (forall (x)
    (implies
     (and
      (q3527217-real-member-p ctx x)
      (q3527217-real-set-member-p ctx set-tag x))
     (q3527217-real-leq ctx x bound))))

(defun-sk q3527217-real-bounded-above-p (ctx set-tag)
  (exists (bound)
    (and
     (q3527217-real-member-p ctx bound)
     (q3527217-real-upper-bound-p
      ctx set-tag bound))))

(defun-sk q3527217-real-least-upper-bound-p
    (ctx set-tag supremum)
  (forall (bound)
    (implies
     (and
      (q3527217-real-member-p ctx bound)
      (q3527217-real-upper-bound-p
       ctx set-tag bound))
     (q3527217-real-leq ctx supremum bound))))

(defun q3527217-real-supremum-p
    (ctx set-tag supremum)
  (and
   (q3527217-real-member-p ctx supremum)
   (q3527217-real-upper-bound-p
    ctx set-tag supremum)
   (q3527217-real-least-upper-bound-p
    ctx set-tag supremum)))

(defun-sk q3527217-real-supremum-exists-p
    (ctx set-tag)
  (exists (supremum)
    (q3527217-real-supremum-p
     ctx set-tag supremum)))

(defun-sk q3527217-real-dedekind-complete-p (ctx)
  (forall (set-tag)
    (implies
     (and
      (q3527217-valid-real-set-p ctx set-tag)
      (q3527217-real-set-nonempty-p ctx set-tag)
      (q3527217-real-bounded-above-p ctx set-tag))
     (q3527217-real-supremum-exists-p
      ctx set-tag))))

(defun q3527217-real-field-p (ctx)
  (let ((zero (q3527217-real-zero ctx))
        (one (q3527217-real-one ctx)))
    (and
     (q3527217-real-member-p ctx zero)
     (q3527217-real-member-p ctx one)
     (not (equal zero one))
     (q3527217-real-less ctx zero one)
     (q3527217-real-field-laws-p ctx)
     (q3527217-real-order-laws-p ctx)
     (q3527217-real-dedekind-complete-p ctx))))

;; The arbitrary additive commutative group and real module.

(defstub q3527217-vector-member-p (ctx value) t)
(defstub q3527217-vector-zero (ctx) t)
(defstub q3527217-vector-add (ctx left right) t)
(defstub q3527217-vector-negate (ctx value) t)
(defstub q3527217-vector-smul (ctx scalar vector) t)

(defun-sk q3527217-add-comm-group-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q3527217-vector-member-p ctx x)
      (q3527217-vector-member-p ctx y)
      (q3527217-vector-member-p ctx z))
     (let ((zero (q3527217-vector-zero ctx)))
       (and
        (q3527217-vector-member-p
         ctx (q3527217-vector-add ctx x y))
        (q3527217-vector-member-p
         ctx (q3527217-vector-negate ctx x))
        (equal
         (q3527217-vector-add
          ctx (q3527217-vector-add ctx x y) z)
         (q3527217-vector-add
          ctx x (q3527217-vector-add ctx y z)))
        (equal
         (q3527217-vector-add ctx x y)
         (q3527217-vector-add ctx y x))
        (equal
         (q3527217-vector-add ctx x zero)
         x)
        (equal
         (q3527217-vector-add
          ctx x (q3527217-vector-negate ctx x))
         zero))))))

(defun-sk q3527217-module-laws-p (ctx)
  (forall (a b x y)
    (implies
     (and
      (q3527217-real-member-p ctx a)
      (q3527217-real-member-p ctx b)
      (q3527217-vector-member-p ctx x)
      (q3527217-vector-member-p ctx y))
     (and
      (q3527217-vector-member-p
       ctx (q3527217-vector-smul ctx a x))
      (equal
       (q3527217-vector-smul
        ctx (q3527217-real-one ctx) x)
       x)
      (equal
       (q3527217-vector-smul
        ctx (q3527217-real-multiply ctx a b) x)
       (q3527217-vector-smul
        ctx a (q3527217-vector-smul ctx b x)))
      (equal
       (q3527217-vector-smul
        ctx (q3527217-real-add ctx a b) x)
       (q3527217-vector-add
        ctx
        (q3527217-vector-smul ctx a x)
        (q3527217-vector-smul ctx b x)))
      (equal
       (q3527217-vector-smul
        ctx a (q3527217-vector-add ctx x y))
       (q3527217-vector-add
        ctx
        (q3527217-vector-smul ctx a x)
        (q3527217-vector-smul ctx a y)))
      (equal
       (q3527217-vector-smul
        ctx (q3527217-real-zero ctx) x)
       (q3527217-vector-zero ctx))
      (equal
       (q3527217-vector-smul
        ctx a (q3527217-vector-zero ctx))
       (q3527217-vector-zero ctx))))))

(defun q3527217-real-vector-space-p (ctx)
  (and
   (q3527217-vector-member-p
    ctx (q3527217-vector-zero ctx))
   (q3527217-add-comm-group-laws-p ctx)
   (q3527217-module-laws-p ctx)))

;; Arbitrary pointed cones and linear subspaces.

(defstub q3527217-cone-member-p
  (ctx cone-tag vector)
  t)

(defstub q3527217-subspace-member-p
  (ctx subspace-tag vector)
  t)

(defun-sk q3527217-pointed-cone-laws-p
    (ctx cone-tag)
  (forall (a x y)
    (and
     (implies
      (q3527217-cone-member-p ctx cone-tag x)
      (q3527217-vector-member-p ctx x))
     (q3527217-cone-member-p
      ctx cone-tag (q3527217-vector-zero ctx))
     (implies
      (and
       (q3527217-cone-member-p ctx cone-tag x)
       (q3527217-cone-member-p ctx cone-tag y))
      (q3527217-cone-member-p
       ctx cone-tag
       (q3527217-vector-add ctx x y)))
     (implies
      (and
       (q3527217-real-member-p ctx a)
       (q3527217-real-leq
        ctx (q3527217-real-zero ctx) a)
       (q3527217-cone-member-p ctx cone-tag x))
      (q3527217-cone-member-p
       ctx cone-tag
       (q3527217-vector-smul ctx a x))))))

(defun-sk q3527217-subspace-laws-p
    (ctx subspace-tag)
  (forall (a x y)
    (and
     (implies
      (q3527217-subspace-member-p
       ctx subspace-tag x)
      (q3527217-vector-member-p ctx x))
     (q3527217-subspace-member-p
      ctx subspace-tag (q3527217-vector-zero ctx))
     (implies
      (and
       (q3527217-subspace-member-p
        ctx subspace-tag x)
       (q3527217-subspace-member-p
        ctx subspace-tag y))
      (q3527217-subspace-member-p
       ctx subspace-tag
       (q3527217-vector-add ctx x y)))
     (implies
      (and
       (q3527217-real-member-p ctx a)
       (q3527217-subspace-member-p
        ctx subspace-tag x))
      (q3527217-subspace-member-p
       ctx subspace-tag
       (q3527217-vector-smul ctx a x))))))

;; The source LinearPMap is represented by its arbitrary subspace domain and
;; its scalar-valued function tag. Extension tags use the same value
;; interface, while the existential quantifier below keeps the extension
;; witness internal to the theorem conclusion.

(defstub q3527217-functional-value
  (ctx functional-tag vector)
  t)

(defun-sk q3527217-partial-linear-functional-p
    (ctx subspace-tag functional-tag)
  (forall (a x y)
    (and
     (implies
      (q3527217-subspace-member-p
       ctx subspace-tag x)
      (q3527217-real-member-p
       ctx
       (q3527217-functional-value
        ctx functional-tag x)))
     (implies
      (and
       (q3527217-subspace-member-p
        ctx subspace-tag x)
       (q3527217-subspace-member-p
        ctx subspace-tag y))
      (equal
       (q3527217-functional-value
        ctx functional-tag
        (q3527217-vector-add ctx x y))
       (q3527217-real-add
        ctx
        (q3527217-functional-value
         ctx functional-tag x)
        (q3527217-functional-value
         ctx functional-tag y))))
     (implies
      (and
       (q3527217-real-member-p ctx a)
       (q3527217-subspace-member-p
        ctx subspace-tag x))
      (equal
       (q3527217-functional-value
        ctx functional-tag
        (q3527217-vector-smul ctx a x))
       (q3527217-real-multiply
        ctx
        a
        (q3527217-functional-value
         ctx functional-tag x)))))))

(defun-sk q3527217-full-linear-functional-p
    (ctx functional-tag)
  (forall (a x y)
    (and
     (implies
      (q3527217-vector-member-p ctx x)
      (q3527217-real-member-p
       ctx
       (q3527217-functional-value
        ctx functional-tag x)))
     (implies
      (and
       (q3527217-vector-member-p ctx x)
       (q3527217-vector-member-p ctx y))
      (equal
       (q3527217-functional-value
        ctx functional-tag
        (q3527217-vector-add ctx x y))
       (q3527217-real-add
        ctx
        (q3527217-functional-value
         ctx functional-tag x)
        (q3527217-functional-value
         ctx functional-tag y))))
     (implies
      (and
       (q3527217-real-member-p ctx a)
       (q3527217-vector-member-p ctx x))
      (equal
       (q3527217-functional-value
        ctx functional-tag
        (q3527217-vector-smul ctx a x))
       (q3527217-real-multiply
        ctx
        a
        (q3527217-functional-value
         ctx functional-tag x)))))))

;; The two source hypotheses: nonnegativity on domain intersect cone, and
;; for every y an x in the domain with x + y in the cone.

(defun-sk q3527217-partial-nonnegative-on-cone-p
    (ctx cone-tag subspace-tag functional-tag)
  (forall (x)
    (implies
     (and
      (q3527217-subspace-member-p
       ctx subspace-tag x)
      (q3527217-cone-member-p ctx cone-tag x))
     (q3527217-real-leq
      ctx
      (q3527217-real-zero ctx)
      (q3527217-functional-value
       ctx functional-tag x)))))

(defun-sk q3527217-domain-shift-into-cone-exists-p
    (ctx cone-tag subspace-tag y)
  (exists (x)
    (and
     (q3527217-subspace-member-p
      ctx subspace-tag x)
     (q3527217-cone-member-p
      ctx
      cone-tag
      (q3527217-vector-add ctx x y)))))

(defun-sk q3527217-subspace-plus-cone-covers-p
    (ctx cone-tag subspace-tag)
  (forall (y)
    (implies
     (q3527217-vector-member-p ctx y)
     (q3527217-domain-shift-into-cone-exists-p
      ctx cone-tag subspace-tag y))))

;; The source conclusion: an internally existential global linear functional
;; agrees with the partial one throughout its domain and is nonnegative on
;; every element of the cone.

(defun-sk q3527217-extension-agrees-p
    (ctx subspace-tag original extension)
  (forall (x)
    (implies
     (q3527217-subspace-member-p
      ctx subspace-tag x)
     (equal
      (q3527217-functional-value ctx extension x)
      (q3527217-functional-value ctx original x)))))

(defun-sk q3527217-functional-nonnegative-on-cone-p
    (ctx cone-tag functional-tag)
  (forall (x)
    (implies
     (q3527217-cone-member-p ctx cone-tag x)
     (q3527217-real-leq
      ctx
      (q3527217-real-zero ctx)
      (q3527217-functional-value
       ctx functional-tag x)))))

(defun-sk q3527217-riesz-extension-exists-p
    (ctx cone-tag subspace-tag original)
  (exists (extension)
    (and
     (q3527217-full-linear-functional-p ctx extension)
     (q3527217-extension-agrees-p
      ctx subspace-tag original extension)
     (q3527217-functional-nonnegative-on-cone-p
      ctx cone-tag extension))))

(defun-sk
    thousand-theorems-q3527217-m-riesz-extension-theorem-statement ()
  (forall (ctx cone-tag subspace-tag functional-tag)
    (implies
     (and
      (q3527217-real-field-p ctx)
      (q3527217-real-vector-space-p ctx)
      (q3527217-pointed-cone-laws-p ctx cone-tag)
      (q3527217-subspace-laws-p ctx subspace-tag)
      (q3527217-partial-linear-functional-p
       ctx subspace-tag functional-tag)
      (q3527217-partial-nonnegative-on-cone-p
       ctx cone-tag subspace-tag functional-tag)
      (q3527217-subspace-plus-cone-covers-p
       ctx cone-tag subspace-tag))
     (q3527217-riesz-extension-exists-p
      ctx cone-tag subspace-tag functional-tag))))

(value-triple :itpeval-statement-checked)
:q
