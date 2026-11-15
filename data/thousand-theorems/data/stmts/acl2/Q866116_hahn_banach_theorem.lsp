;; Statement-only formalization of thousand-theorems corpus artifact Q866116,
;; "Hahn–Banach theorem": every continuous linear functional on a subspace of
;; a real or complex seminormed space extends to the whole space with exactly
;; the same operator norm. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A context tag presents the complete ordered real field, an RCLike scalar
;; field, and an arbitrary seminormed vector space. Subspaces and functionals
;; are arbitrary tags interpreted by conservative generic symbols. All
;; algebraic, order, norm, typing, subspace, linearity, and boundedness laws
;; are explicit. For linear maps over an RCLike field, a global action bound
;; is equivalent to continuity. The operator norm is characterized as the
;; least nonnegative action bound.

;; The complete ordered real field underlying the scalar norm.

(defstub q866116-real-member-p (ctx x) t)
(defstub q866116-real-zero (ctx) t)
(defstub q866116-real-one (ctx) t)
(defstub q866116-real-add (ctx x y) t)
(defstub q866116-real-mul (ctx x y) t)
(defstub q866116-real-neg (ctx x) t)
(defstub q866116-real-inv (ctx x) t)
(defstub q866116-real-lt (ctx x y) t)
(defstub q866116-real-set-member-p (ctx set-tag x) t)

(defun q866116-real-le-p (ctx x y)
  (not (q866116-real-lt ctx y x)))

(defun-sk q866116-real-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q866116-real-member-p ctx x)
      (q866116-real-member-p ctx y)
      (q866116-real-member-p ctx z))
     (let ((zero (q866116-real-zero ctx))
           (one (q866116-real-one ctx)))
       (and
        (q866116-real-member-p
         ctx (q866116-real-add ctx x y))
        (q866116-real-member-p
         ctx (q866116-real-mul ctx x y))
        (q866116-real-member-p
         ctx (q866116-real-neg ctx x))
        (q866116-real-member-p
         ctx (q866116-real-inv ctx x))
        (equal
         (q866116-real-add
          ctx (q866116-real-add ctx x y) z)
         (q866116-real-add
          ctx x (q866116-real-add ctx y z)))
        (equal
         (q866116-real-add ctx x y)
         (q866116-real-add ctx y x))
        (equal (q866116-real-add ctx x zero) x)
        (equal
         (q866116-real-add
          ctx x (q866116-real-neg ctx x))
         zero)
        (equal
         (q866116-real-mul
          ctx (q866116-real-mul ctx x y) z)
         (q866116-real-mul
          ctx x (q866116-real-mul ctx y z)))
        (equal
         (q866116-real-mul ctx x y)
         (q866116-real-mul ctx y x))
        (equal (q866116-real-mul ctx x one) x)
        (equal (q866116-real-inv ctx zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q866116-real-mul
           ctx x (q866116-real-inv ctx x))
          one))
        (equal
         (q866116-real-mul
          ctx x (q866116-real-add ctx y z))
         (q866116-real-add
          ctx
          (q866116-real-mul ctx x y)
          (q866116-real-mul ctx x z))))))))

(defun-sk q866116-real-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q866116-real-member-p ctx x)
      (q866116-real-member-p ctx y)
      (q866116-real-member-p ctx z))
     (let ((zero (q866116-real-zero ctx)))
       (and
        (not (q866116-real-lt ctx x x))
        (or
         (equal x y)
         (q866116-real-lt ctx x y)
         (q866116-real-lt ctx y x))
        (implies
         (and
          (q866116-real-lt ctx x y)
          (q866116-real-lt ctx y z))
         (q866116-real-lt ctx x z))
        (implies
         (q866116-real-lt ctx x y)
         (q866116-real-lt
          ctx
          (q866116-real-add ctx x z)
          (q866116-real-add ctx y z)))
        (implies
         (and
          (q866116-real-lt ctx zero x)
          (q866116-real-lt ctx zero y))
         (q866116-real-lt
          ctx zero (q866116-real-mul ctx x y))))))))

(defun-sk q866116-real-set-nonempty-p (ctx set-tag)
  (exists (x)
    (and
     (q866116-real-member-p ctx x)
     (q866116-real-set-member-p ctx set-tag x))))

(defun-sk q866116-real-upper-bound-p
    (ctx set-tag bound)
  (forall (x)
    (implies
     (and
      (q866116-real-member-p ctx x)
      (q866116-real-set-member-p ctx set-tag x))
     (q866116-real-le-p ctx x bound))))

(defun-sk q866116-real-bounded-above-p (ctx set-tag)
  (exists (bound)
    (and
     (q866116-real-member-p ctx bound)
     (q866116-real-upper-bound-p
      ctx set-tag bound))))

(defun-sk q866116-real-supremum-p
    (ctx set-tag supremum)
  (forall (bound)
    (and
     (q866116-real-member-p ctx supremum)
     (q866116-real-upper-bound-p
      ctx set-tag supremum)
     (implies
      (and
       (q866116-real-member-p ctx bound)
       (q866116-real-upper-bound-p
        ctx set-tag bound))
      (q866116-real-le-p ctx supremum bound)))))

(defun-sk q866116-real-supremum-exists-p
    (ctx set-tag)
  (exists (supremum)
    (q866116-real-supremum-p
     ctx set-tag supremum)))

(defun-sk q866116-real-complete-p (ctx)
  (forall (set-tag)
    (implies
     (and
      (q866116-real-set-nonempty-p ctx set-tag)
      (q866116-real-bounded-above-p ctx set-tag))
     (q866116-real-supremum-exists-p
      ctx set-tag))))

(defun q866116-real-field-p (ctx)
  (let ((zero (q866116-real-zero ctx))
        (one (q866116-real-one ctx)))
    (and
     (q866116-real-member-p ctx zero)
     (q866116-real-member-p ctx one)
     (not (equal zero one))
     (q866116-real-lt ctx zero one)
     (q866116-real-field-laws-p ctx)
     (q866116-real-order-laws-p ctx)
     (q866116-real-complete-p ctx))))

;; An RCLike scalar field: either the real field or its quadratic complex
;; extension, together with the usual absolute-value norm.

(defstub q866116-complexp (ctx) t)
(defstub q866116-scalar-member-p (ctx x) t)
(defstub q866116-scalar-zero (ctx) t)
(defstub q866116-scalar-one (ctx) t)
(defstub q866116-scalar-add (ctx x y) t)
(defstub q866116-scalar-mul (ctx x y) t)
(defstub q866116-scalar-neg (ctx x) t)
(defstub q866116-scalar-inv (ctx x) t)
(defstub q866116-scalar-conj (ctx x) t)
(defstub q866116-of-real (ctx x) t)
(defstub q866116-real-part (ctx x) t)
(defstub q866116-imag-part (ctx x) t)
(defstub q866116-imaginary-unit (ctx) t)
(defstub q866116-scalar-norm (ctx x) t)

(defun-sk q866116-scalar-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q866116-scalar-member-p ctx x)
      (q866116-scalar-member-p ctx y)
      (q866116-scalar-member-p ctx z))
     (let ((zero (q866116-scalar-zero ctx))
           (one (q866116-scalar-one ctx)))
       (and
        (q866116-scalar-member-p
         ctx (q866116-scalar-add ctx x y))
        (q866116-scalar-member-p
         ctx (q866116-scalar-mul ctx x y))
        (q866116-scalar-member-p
         ctx (q866116-scalar-neg ctx x))
        (q866116-scalar-member-p
         ctx (q866116-scalar-inv ctx x))
        (equal
         (q866116-scalar-add
          ctx (q866116-scalar-add ctx x y) z)
         (q866116-scalar-add
          ctx x (q866116-scalar-add ctx y z)))
        (equal
         (q866116-scalar-add ctx x y)
         (q866116-scalar-add ctx y x))
        (equal (q866116-scalar-add ctx x zero) x)
        (equal
         (q866116-scalar-add
          ctx x (q866116-scalar-neg ctx x))
         zero)
        (equal
         (q866116-scalar-mul
          ctx (q866116-scalar-mul ctx x y) z)
         (q866116-scalar-mul
          ctx x (q866116-scalar-mul ctx y z)))
        (equal
         (q866116-scalar-mul ctx x y)
         (q866116-scalar-mul ctx y x))
        (equal (q866116-scalar-mul ctx x one) x)
        (equal (q866116-scalar-inv ctx zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q866116-scalar-mul
           ctx x (q866116-scalar-inv ctx x))
          one))
        (equal
         (q866116-scalar-mul
          ctx x (q866116-scalar-add ctx y z))
         (q866116-scalar-add
          ctx
          (q866116-scalar-mul ctx x y)
          (q866116-scalar-mul ctx x z))))))))

(defun-sk q866116-real-embedding-laws-p (ctx)
  (forall (r s)
    (implies
     (and
      (q866116-real-member-p ctx r)
      (q866116-real-member-p ctx s))
     (let ((of-r (q866116-of-real ctx r))
           (of-s (q866116-of-real ctx s)))
       (and
        (q866116-scalar-member-p ctx of-r)
        (equal (q866116-real-part ctx of-r) r)
        (equal
         (q866116-imag-part ctx of-r)
         (q866116-real-zero ctx))
        (equal
         (q866116-of-real
          ctx (q866116-real-add ctx r s))
         (q866116-scalar-add ctx of-r of-s))
        (equal
         (q866116-of-real
          ctx (q866116-real-mul ctx r s))
         (q866116-scalar-mul ctx of-r of-s))
        (equal
         (q866116-of-real
          ctx (q866116-real-neg ctx r))
         (q866116-scalar-neg ctx of-r)))))))

(defun-sk q866116-scalar-coordinate-laws-p (ctx)
  (forall (x y)
    (implies
     (and
      (q866116-scalar-member-p ctx x)
      (q866116-scalar-member-p ctx y))
     (let* ((re-x (q866116-real-part ctx x))
            (im-x (q866116-imag-part ctx x))
            (of-re-x (q866116-of-real ctx re-x))
            (of-im-x (q866116-of-real ctx im-x))
            (i (q866116-imaginary-unit ctx))
            (im-coordinate
             (q866116-scalar-mul ctx of-im-x i)))
       (and
        (q866116-real-member-p ctx re-x)
        (q866116-real-member-p ctx im-x)
        (q866116-scalar-member-p
         ctx (q866116-scalar-conj ctx x))
        (equal
         x
         (q866116-scalar-add
          ctx of-re-x im-coordinate))
        (equal
         (q866116-scalar-conj ctx x)
         (q866116-scalar-add
          ctx
          of-re-x
          (q866116-scalar-neg ctx im-coordinate)))
        (equal
         (q866116-scalar-conj
          ctx (q866116-scalar-add ctx x y))
         (q866116-scalar-add
          ctx
          (q866116-scalar-conj ctx x)
          (q866116-scalar-conj ctx y)))
        (equal
         (q866116-scalar-conj
          ctx (q866116-scalar-mul ctx x y))
         (q866116-scalar-mul
          ctx
          (q866116-scalar-conj ctx x)
          (q866116-scalar-conj ctx y)))
        (equal
         (q866116-scalar-conj
          ctx (q866116-scalar-conj ctx x))
         x)
        (if (q866116-complexp ctx)
            t
          (and
           (equal im-x (q866116-real-zero ctx))
           (equal x of-re-x)
           (equal (q866116-scalar-conj ctx x) x))))))))

(defun-sk q866116-scalar-norm-laws-p (ctx)
  (forall (x y)
    (implies
     (and
      (q866116-scalar-member-p ctx x)
      (q866116-scalar-member-p ctx y))
     (let* ((zero-r (q866116-real-zero ctx))
            (zero-k (q866116-scalar-zero ctx))
            (norm-x (q866116-scalar-norm ctx x))
            (norm-y (q866116-scalar-norm ctx y))
            (re-x (q866116-real-part ctx x))
            (im-x (q866116-imag-part ctx x)))
       (and
        (q866116-real-member-p ctx norm-x)
        (q866116-real-member-p ctx norm-y)
        (q866116-real-le-p ctx zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-k))
        (equal
         (q866116-scalar-norm
          ctx (q866116-scalar-neg ctx x))
         norm-x)
        (q866116-real-le-p
         ctx
         (q866116-scalar-norm
          ctx (q866116-scalar-add ctx x y))
         (q866116-real-add ctx norm-x norm-y))
        (equal
         (q866116-scalar-norm
          ctx (q866116-scalar-mul ctx x y))
         (q866116-real-mul ctx norm-x norm-y))
        (equal
         (q866116-real-mul ctx norm-x norm-x)
         (q866116-real-add
          ctx
          (q866116-real-mul ctx re-x re-x)
          (q866116-real-mul ctx im-x im-x))))))))

(defun-sk q866116-large-norm-scalar-exists-p (ctx)
  (exists (x)
    (and
     (q866116-scalar-member-p ctx x)
     (q866116-real-lt
      ctx
      (q866116-real-one ctx)
      (q866116-scalar-norm ctx x)))))

(defun q866116-rclike-field-p (ctx)
  (let ((real-zero (q866116-real-zero ctx))
        (real-one (q866116-real-one ctx))
        (zero (q866116-scalar-zero ctx))
        (one (q866116-scalar-one ctx))
        (i (q866116-imaginary-unit ctx)))
    (and
     (booleanp (q866116-complexp ctx))
     (q866116-real-field-p ctx)
     (q866116-scalar-member-p ctx zero)
     (q866116-scalar-member-p ctx one)
     (not (equal zero one))
     (q866116-scalar-member-p ctx i)
     (equal (q866116-of-real ctx real-zero) zero)
     (equal (q866116-of-real ctx real-one) one)
     (equal (q866116-real-part ctx zero) real-zero)
     (equal (q866116-imag-part ctx zero) real-zero)
     (equal (q866116-real-part ctx one) real-one)
     (equal (q866116-imag-part ctx one) real-zero)
     (q866116-scalar-field-laws-p ctx)
     (q866116-real-embedding-laws-p ctx)
     (q866116-scalar-coordinate-laws-p ctx)
     (q866116-scalar-norm-laws-p ctx)
     (q866116-large-norm-scalar-exists-p ctx)
     (if (q866116-complexp ctx)
         (and
          (equal (q866116-real-part ctx i) real-zero)
          (equal (q866116-imag-part ctx i) real-one)
          (equal
           (q866116-scalar-mul ctx i i)
           (q866116-scalar-neg ctx one)))
       (equal i zero)))))

;; The arbitrary seminormed vector space over the RCLike field.

(defstub q866116-vector-member-p (ctx x) t)
(defstub q866116-vector-zero (ctx) t)
(defstub q866116-vector-add (ctx x y) t)
(defstub q866116-vector-neg (ctx x) t)
(defstub q866116-vector-smul (ctx scalar vector) t)
(defstub q866116-vector-norm (ctx vector) t)

(defun-sk q866116-add-comm-group-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q866116-vector-member-p ctx x)
      (q866116-vector-member-p ctx y)
      (q866116-vector-member-p ctx z))
     (let ((zero (q866116-vector-zero ctx)))
       (and
        (q866116-vector-member-p
         ctx (q866116-vector-add ctx x y))
        (q866116-vector-member-p
         ctx (q866116-vector-neg ctx x))
        (equal
         (q866116-vector-add
          ctx (q866116-vector-add ctx x y) z)
         (q866116-vector-add
          ctx x (q866116-vector-add ctx y z)))
        (equal
         (q866116-vector-add ctx x y)
         (q866116-vector-add ctx y x))
        (equal (q866116-vector-add ctx x zero) x)
        (equal
         (q866116-vector-add
          ctx x (q866116-vector-neg ctx x))
         zero))))))

(defun-sk q866116-seminorm-laws-p (ctx)
  (forall (x y)
    (implies
     (and
      (q866116-vector-member-p ctx x)
      (q866116-vector-member-p ctx y))
     (let ((zero-r (q866116-real-zero ctx))
           (norm-x (q866116-vector-norm ctx x))
           (norm-y (q866116-vector-norm ctx y)))
       (and
        (q866116-real-member-p ctx norm-x)
        (q866116-real-member-p ctx norm-y)
        (q866116-real-le-p ctx zero-r norm-x)
        (equal
         (q866116-vector-norm
          ctx (q866116-vector-zero ctx))
         zero-r)
        (equal
         (q866116-vector-norm
          ctx (q866116-vector-neg ctx x))
         norm-x)
        (q866116-real-le-p
         ctx
         (q866116-vector-norm
          ctx (q866116-vector-add ctx x y))
         (q866116-real-add ctx norm-x norm-y)))))))

(defun-sk q866116-vector-space-laws-p (ctx)
  (forall (a b x y)
    (implies
     (and
      (q866116-scalar-member-p ctx a)
      (q866116-scalar-member-p ctx b)
      (q866116-vector-member-p ctx x)
      (q866116-vector-member-p ctx y))
     (and
      (q866116-vector-member-p
       ctx (q866116-vector-smul ctx a x))
      (equal
       (q866116-vector-smul
        ctx (q866116-scalar-one ctx) x)
       x)
      (equal
       (q866116-vector-smul
        ctx (q866116-scalar-mul ctx a b) x)
       (q866116-vector-smul
        ctx a (q866116-vector-smul ctx b x)))
      (equal
       (q866116-vector-smul
        ctx (q866116-scalar-add ctx a b) x)
       (q866116-vector-add
        ctx
        (q866116-vector-smul ctx a x)
        (q866116-vector-smul ctx b x)))
      (equal
       (q866116-vector-smul
        ctx a (q866116-vector-add ctx x y))
       (q866116-vector-add
        ctx
        (q866116-vector-smul ctx a x)
        (q866116-vector-smul ctx a y)))
      (equal
       (q866116-vector-smul
        ctx (q866116-scalar-zero ctx) x)
       (q866116-vector-zero ctx))
      (equal
       (q866116-vector-smul
        ctx a (q866116-vector-zero ctx))
       (q866116-vector-zero ctx))
      (equal
       (q866116-vector-norm
        ctx (q866116-vector-smul ctx a x))
       (q866116-real-mul
        ctx
        (q866116-scalar-norm ctx a)
        (q866116-vector-norm ctx x)))))))

(defun q866116-seminormed-space-p (ctx)
  (and
   (q866116-vector-member-p
    ctx (q866116-vector-zero ctx))
   (q866116-add-comm-group-laws-p ctx)
   (q866116-seminorm-laws-p ctx)
   (q866116-vector-space-laws-p ctx)))

;; Arbitrary linear subspaces and scalar-valued linear functionals.

(defstub q866116-subspace-member-p
  (ctx subspace-tag vector)
  t)

(defstub q866116-functional-value
  (ctx functional-tag vector)
  t)

(defun-sk q866116-subspace-laws-p
    (ctx subspace-tag)
  (forall (a x y)
    (and
     (implies
      (q866116-subspace-member-p
       ctx subspace-tag x)
      (q866116-vector-member-p ctx x))
     (q866116-subspace-member-p
      ctx subspace-tag (q866116-vector-zero ctx))
     (implies
      (and
       (q866116-subspace-member-p
        ctx subspace-tag x)
       (q866116-subspace-member-p
        ctx subspace-tag y))
      (q866116-subspace-member-p
       ctx subspace-tag
       (q866116-vector-add ctx x y)))
     (implies
      (and
       (q866116-scalar-member-p ctx a)
       (q866116-subspace-member-p
        ctx subspace-tag x))
      (q866116-subspace-member-p
       ctx subspace-tag
       (q866116-vector-smul ctx a x))))))

(defun-sk q866116-subspace-linear-functional-p
    (ctx subspace-tag functional-tag)
  (forall (a x y)
    (implies
     (and
      (q866116-scalar-member-p ctx a)
      (q866116-subspace-member-p
       ctx subspace-tag x)
      (q866116-subspace-member-p
       ctx subspace-tag y))
     (and
      (q866116-scalar-member-p
       ctx
       (q866116-functional-value
        ctx functional-tag x))
      (equal
       (q866116-functional-value
        ctx functional-tag
        (q866116-vector-add ctx x y))
       (q866116-scalar-add
        ctx
        (q866116-functional-value
         ctx functional-tag x)
        (q866116-functional-value
         ctx functional-tag y)))
      (equal
       (q866116-functional-value
        ctx functional-tag
        (q866116-vector-smul ctx a x))
       (q866116-scalar-mul
        ctx a
        (q866116-functional-value
         ctx functional-tag x)))))))

(defun-sk q866116-full-linear-functional-p
    (ctx functional-tag)
  (forall (a x y)
    (implies
     (and
      (q866116-scalar-member-p ctx a)
      (q866116-vector-member-p ctx x)
      (q866116-vector-member-p ctx y))
     (and
      (q866116-scalar-member-p
       ctx
       (q866116-functional-value
        ctx functional-tag x))
      (equal
       (q866116-functional-value
        ctx functional-tag
        (q866116-vector-add ctx x y))
       (q866116-scalar-add
        ctx
        (q866116-functional-value
         ctx functional-tag x)
        (q866116-functional-value
         ctx functional-tag y)))
      (equal
       (q866116-functional-value
        ctx functional-tag
        (q866116-vector-smul ctx a x))
       (q866116-scalar-mul
        ctx a
        (q866116-functional-value
         ctx functional-tag x)))))))

(defun-sk q866116-subspace-action-bound-p
    (ctx subspace-tag functional-tag bound)
  (forall (x)
    (implies
     (q866116-subspace-member-p
      ctx subspace-tag x)
     (q866116-real-le-p
      ctx
      (q866116-scalar-norm
       ctx
       (q866116-functional-value
        ctx functional-tag x))
      (q866116-real-mul
       ctx bound (q866116-vector-norm ctx x))))))

(defun-sk q866116-full-action-bound-p
    (ctx functional-tag bound)
  (forall (x)
    (implies
     (q866116-vector-member-p ctx x)
     (q866116-real-le-p
      ctx
      (q866116-scalar-norm
       ctx
       (q866116-functional-value
        ctx functional-tag x))
      (q866116-real-mul
       ctx bound (q866116-vector-norm ctx x))))))

(defun-sk q866116-subspace-bound-exists-p
    (ctx subspace-tag functional-tag)
  (exists (bound)
    (and
     (q866116-real-member-p ctx bound)
     (q866116-real-le-p
      ctx (q866116-real-zero ctx) bound)
     (q866116-subspace-action-bound-p
      ctx subspace-tag functional-tag bound))))

(defun-sk q866116-full-bound-exists-p
    (ctx functional-tag)
  (exists (bound)
    (and
     (q866116-real-member-p ctx bound)
     (q866116-real-le-p
      ctx (q866116-real-zero ctx) bound)
     (q866116-full-action-bound-p
      ctx functional-tag bound))))

(defun q866116-subspace-strong-dual-p
    (ctx subspace-tag functional-tag)
  (and
   (q866116-subspace-linear-functional-p
    ctx subspace-tag functional-tag)
   (q866116-subspace-bound-exists-p
    ctx subspace-tag functional-tag)))

(defun q866116-full-strong-dual-p
    (ctx functional-tag)
  (and
   (q866116-full-linear-functional-p
    ctx functional-tag)
   (q866116-full-bound-exists-p
    ctx functional-tag)))

;; Least action bounds are the operator norms of the two continuous linear
;; maps. Sharing the same least bound is exactly equality of their norms.

(defun-sk q866116-subspace-least-bound-p
    (ctx subspace-tag functional-tag norm-value)
  (forall (bound)
    (implies
     (and
      (q866116-real-member-p ctx bound)
      (q866116-real-le-p
       ctx (q866116-real-zero ctx) bound)
      (q866116-subspace-action-bound-p
       ctx subspace-tag functional-tag bound))
     (q866116-real-le-p ctx norm-value bound))))

(defun q866116-subspace-operator-norm-p
    (ctx subspace-tag functional-tag norm-value)
  (and
   (q866116-real-member-p ctx norm-value)
   (q866116-real-le-p
    ctx (q866116-real-zero ctx) norm-value)
   (q866116-subspace-action-bound-p
    ctx subspace-tag functional-tag norm-value)
   (q866116-subspace-least-bound-p
    ctx subspace-tag functional-tag norm-value)))

(defun-sk q866116-full-least-bound-p
    (ctx functional-tag norm-value)
  (forall (bound)
    (implies
     (and
      (q866116-real-member-p ctx bound)
      (q866116-real-le-p
       ctx (q866116-real-zero ctx) bound)
      (q866116-full-action-bound-p
       ctx functional-tag bound))
     (q866116-real-le-p ctx norm-value bound))))

(defun q866116-full-operator-norm-p
    (ctx functional-tag norm-value)
  (and
   (q866116-real-member-p ctx norm-value)
   (q866116-real-le-p
    ctx (q866116-real-zero ctx) norm-value)
   (q866116-full-action-bound-p
    ctx functional-tag norm-value)
   (q866116-full-least-bound-p
    ctx functional-tag norm-value)))

(defun-sk q866116-same-operator-norm-p
    (ctx subspace-tag original extension)
  (exists (norm-value)
    (and
     (q866116-subspace-operator-norm-p
      ctx subspace-tag original norm-value)
     (q866116-full-operator-norm-p
      ctx extension norm-value))))

(defun-sk q866116-extends-p
    (ctx subspace-tag original extension)
  (forall (x)
    (implies
     (q866116-subspace-member-p
      ctx subspace-tag x)
     (equal
      (q866116-functional-value
       ctx extension x)
      (q866116-functional-value
       ctx original x)))))

(defun-sk q866116-norm-preserving-extension-exists-p
    (ctx subspace-tag original)
  (exists (extension)
    (and
     (q866116-full-strong-dual-p ctx extension)
     (q866116-extends-p
      ctx subspace-tag original extension)
     (q866116-same-operator-norm-p
      ctx subspace-tag original extension))))

(defun-sk
    thousand-theorems-q866116-hahn-banach-theorem-statement ()
  (forall (ctx subspace-tag functional-tag)
    (implies
     (and
      (q866116-rclike-field-p ctx)
      (q866116-seminormed-space-p ctx)
      (q866116-subspace-laws-p ctx subspace-tag)
      (q866116-subspace-strong-dual-p
       ctx subspace-tag functional-tag))
     (q866116-norm-preserving-extension-exists-p
      ctx subspace-tag functional-tag))))

(value-triple :itpeval-statement-checked)
:q
