;; Statement-only formalization of thousand-theorems corpus artifact Q1357684,
;; "Riesz representation theorem": every continuous linear functional on a
;; real or complex Hilbert space is inner product with a unique vector. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A context tag indexes arbitrary real and scalar fields, an arbitrary vector
;; carrier, their operations, inner product, sequences, and linear
;; functionals. Conservative generic symbols avoid finite carriers or tables;
;; every algebraic, order, completeness, continuity, and typing law used by
;; the statement is explicit below.

;; The complete ordered real field underlying an RCLike scalar field.

(defstub q1357684-real-member-p (ctx x) t)
(defstub q1357684-real-zero (ctx) t)
(defstub q1357684-real-one (ctx) t)
(defstub q1357684-real-add (ctx x y) t)
(defstub q1357684-real-mul (ctx x y) t)
(defstub q1357684-real-neg (ctx x) t)
(defstub q1357684-real-inv (ctx x) t)
(defstub q1357684-real-lt (ctx x y) t)
(defstub q1357684-real-set-member-p (ctx set-tag x) t)

(defun q1357684-real-le-p (ctx x y)
  (not (q1357684-real-lt ctx y x)))

(defun q1357684-positive-real-p (ctx x)
  (and
   (q1357684-real-member-p ctx x)
   (q1357684-real-lt
    ctx (q1357684-real-zero ctx) x)))

(defun-sk q1357684-real-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q1357684-real-member-p ctx x)
      (q1357684-real-member-p ctx y)
      (q1357684-real-member-p ctx z))
     (let ((zero (q1357684-real-zero ctx))
           (one (q1357684-real-one ctx)))
       (and
        (q1357684-real-member-p
         ctx (q1357684-real-add ctx x y))
        (q1357684-real-member-p
         ctx (q1357684-real-mul ctx x y))
        (q1357684-real-member-p
         ctx (q1357684-real-neg ctx x))
        (implies
         (not (equal x zero))
         (q1357684-real-member-p
          ctx (q1357684-real-inv ctx x)))
        (equal
         (q1357684-real-add
          ctx (q1357684-real-add ctx x y) z)
         (q1357684-real-add
          ctx x (q1357684-real-add ctx y z)))
        (equal
         (q1357684-real-add ctx x y)
         (q1357684-real-add ctx y x))
        (equal (q1357684-real-add ctx x zero) x)
        (equal
         (q1357684-real-add
          ctx x (q1357684-real-neg ctx x))
         zero)
        (equal
         (q1357684-real-mul
          ctx (q1357684-real-mul ctx x y) z)
         (q1357684-real-mul
          ctx x (q1357684-real-mul ctx y z)))
        (equal
         (q1357684-real-mul ctx x y)
         (q1357684-real-mul ctx y x))
        (equal (q1357684-real-mul ctx x one) x)
        (equal (q1357684-real-inv ctx zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1357684-real-mul
           ctx x (q1357684-real-inv ctx x))
          one))
        (equal
         (q1357684-real-mul
          ctx x (q1357684-real-add ctx y z))
         (q1357684-real-add
          ctx
          (q1357684-real-mul ctx x y)
          (q1357684-real-mul ctx x z))))))))

(defun-sk q1357684-real-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q1357684-real-member-p ctx x)
      (q1357684-real-member-p ctx y)
      (q1357684-real-member-p ctx z))
     (let ((zero (q1357684-real-zero ctx)))
       (and
        (not (q1357684-real-lt ctx x x))
        (or
         (equal x y)
         (q1357684-real-lt ctx x y)
         (q1357684-real-lt ctx y x))
        (implies
         (and
          (q1357684-real-lt ctx x y)
          (q1357684-real-lt ctx y z))
         (q1357684-real-lt ctx x z))
        (implies
         (q1357684-real-lt ctx x y)
         (q1357684-real-lt
          ctx
          (q1357684-real-add ctx x z)
          (q1357684-real-add ctx y z)))
        (implies
         (and
          (q1357684-real-lt ctx zero x)
          (q1357684-real-lt ctx zero y))
         (q1357684-real-lt
          ctx zero (q1357684-real-mul ctx x y))))))))

(defun-sk q1357684-real-set-nonempty-p (ctx set-tag)
  (exists (x)
    (and
     (q1357684-real-member-p ctx x)
     (q1357684-real-set-member-p ctx set-tag x))))

(defun-sk q1357684-real-upper-bound-p (ctx set-tag upper)
  (forall (x)
    (implies
     (and
      (q1357684-real-member-p ctx x)
      (q1357684-real-set-member-p ctx set-tag x))
     (q1357684-real-le-p ctx x upper))))

(defun-sk q1357684-real-bounded-above-p (ctx set-tag)
  (exists (upper)
    (and
     (q1357684-real-member-p ctx upper)
     (q1357684-real-upper-bound-p
      ctx set-tag upper))))

(defun-sk q1357684-real-least-upper-bound-p
    (ctx set-tag supremum)
  (forall (upper)
    (implies
     (and
      (q1357684-real-member-p ctx upper)
      (q1357684-real-upper-bound-p
       ctx set-tag upper))
     (q1357684-real-le-p ctx supremum upper))))

(defun q1357684-real-supremum-p (ctx set-tag supremum)
  (and
   (q1357684-real-member-p ctx supremum)
   (q1357684-real-upper-bound-p
    ctx set-tag supremum)
   (q1357684-real-least-upper-bound-p
    ctx set-tag supremum)))

(defun-sk q1357684-real-has-supremum-p (ctx set-tag)
  (exists (supremum)
    (q1357684-real-supremum-p
     ctx set-tag supremum)))

(defun-sk q1357684-real-complete-p (ctx)
  (forall (set-tag)
    (implies
     (and
      (q1357684-real-set-nonempty-p ctx set-tag)
      (q1357684-real-bounded-above-p ctx set-tag))
     (q1357684-real-has-supremum-p
      ctx set-tag))))

(defun q1357684-real-field-p (ctx)
  (let ((zero (q1357684-real-zero ctx))
        (one (q1357684-real-one ctx)))
    (and
     (q1357684-real-member-p ctx zero)
     (q1357684-real-member-p ctx one)
     (not (equal zero one))
     (q1357684-real-lt ctx zero one)
     (q1357684-real-field-laws-p ctx)
     (q1357684-real-order-laws-p ctx)
     (q1357684-real-complete-p ctx))))

;; The scalar field is either the real field or its quadratic complexification.

(defstub q1357684-complexp (ctx) t)
(defstub q1357684-scalar-member-p (ctx x) t)
(defstub q1357684-scalar-zero (ctx) t)
(defstub q1357684-scalar-one (ctx) t)
(defstub q1357684-scalar-add (ctx x y) t)
(defstub q1357684-scalar-mul (ctx x y) t)
(defstub q1357684-scalar-neg (ctx x) t)
(defstub q1357684-scalar-inv (ctx x) t)
(defstub q1357684-star (ctx x) t)
(defstub q1357684-of-real (ctx x) t)
(defstub q1357684-real-part (ctx x) t)
(defstub q1357684-imag-part (ctx x) t)
(defstub q1357684-imaginary-unit (ctx) t)

(defun-sk q1357684-scalar-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (q1357684-scalar-member-p ctx x)
      (q1357684-scalar-member-p ctx y)
      (q1357684-scalar-member-p ctx z))
     (let ((zero (q1357684-scalar-zero ctx))
           (one (q1357684-scalar-one ctx)))
       (and
        (q1357684-scalar-member-p
         ctx (q1357684-scalar-add ctx x y))
        (q1357684-scalar-member-p
         ctx (q1357684-scalar-mul ctx x y))
        (q1357684-scalar-member-p
         ctx (q1357684-scalar-neg ctx x))
        (implies
         (not (equal x zero))
         (q1357684-scalar-member-p
          ctx (q1357684-scalar-inv ctx x)))
        (equal
         (q1357684-scalar-add
          ctx (q1357684-scalar-add ctx x y) z)
         (q1357684-scalar-add
          ctx x (q1357684-scalar-add ctx y z)))
        (equal
         (q1357684-scalar-add ctx x y)
         (q1357684-scalar-add ctx y x))
        (equal (q1357684-scalar-add ctx x zero) x)
        (equal
         (q1357684-scalar-add
          ctx x (q1357684-scalar-neg ctx x))
         zero)
        (equal
         (q1357684-scalar-mul
          ctx (q1357684-scalar-mul ctx x y) z)
         (q1357684-scalar-mul
          ctx x (q1357684-scalar-mul ctx y z)))
        (equal
         (q1357684-scalar-mul ctx x y)
         (q1357684-scalar-mul ctx y x))
        (equal (q1357684-scalar-mul ctx x one) x)
        (equal (q1357684-scalar-inv ctx zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1357684-scalar-mul
           ctx x (q1357684-scalar-inv ctx x))
          one))
        (equal
         (q1357684-scalar-mul
          ctx x (q1357684-scalar-add ctx y z))
         (q1357684-scalar-add
          ctx
          (q1357684-scalar-mul ctx x y)
          (q1357684-scalar-mul ctx x z))))))))

(defun-sk q1357684-real-embedding-laws-p (ctx)
  (forall (r s)
    (implies
     (and
      (q1357684-real-member-p ctx r)
      (q1357684-real-member-p ctx s))
     (let ((of-r (q1357684-of-real ctx r))
           (of-s (q1357684-of-real ctx s)))
       (and
        (q1357684-scalar-member-p ctx of-r)
        (equal
         (q1357684-real-part ctx of-r) r)
        (equal
         (q1357684-imag-part ctx of-r)
         (q1357684-real-zero ctx))
        (equal
         (q1357684-of-real
          ctx (q1357684-real-add ctx r s))
         (q1357684-scalar-add ctx of-r of-s))
        (equal
         (q1357684-of-real
          ctx (q1357684-real-mul ctx r s))
         (q1357684-scalar-mul ctx of-r of-s))
        (equal
         (q1357684-of-real
          ctx (q1357684-real-neg ctx r))
         (q1357684-scalar-neg ctx of-r)))))))

(defun-sk q1357684-scalar-coordinate-laws-p (ctx)
  (forall (x y)
    (implies
     (and
      (q1357684-scalar-member-p ctx x)
      (q1357684-scalar-member-p ctx y))
     (let* ((re-x (q1357684-real-part ctx x))
            (im-x (q1357684-imag-part ctx x))
            (of-re-x (q1357684-of-real ctx re-x))
            (of-im-x (q1357684-of-real ctx im-x))
            (i (q1357684-imaginary-unit ctx))
            (im-coordinate
             (q1357684-scalar-mul ctx of-im-x i)))
       (and
        (q1357684-real-member-p ctx re-x)
        (q1357684-real-member-p ctx im-x)
        (q1357684-scalar-member-p
         ctx (q1357684-star ctx x))
        (equal
         x
         (q1357684-scalar-add
          ctx of-re-x im-coordinate))
        (equal
         (q1357684-star ctx x)
         (q1357684-scalar-add
          ctx
          of-re-x
          (q1357684-scalar-neg ctx im-coordinate)))
        (equal
         (q1357684-star
          ctx (q1357684-scalar-add ctx x y))
         (q1357684-scalar-add
          ctx
          (q1357684-star ctx x)
          (q1357684-star ctx y)))
        (equal
         (q1357684-star
          ctx (q1357684-scalar-mul ctx x y))
         (q1357684-scalar-mul
          ctx
          (q1357684-star ctx x)
          (q1357684-star ctx y)))
        (equal
         (q1357684-star
          ctx (q1357684-star ctx x))
         x)
        (if (q1357684-complexp ctx)
            t
          (and
           (equal im-x (q1357684-real-zero ctx))
           (equal x of-re-x)
           (equal (q1357684-star ctx x) x))))))))

(defun q1357684-rclike-field-p (ctx)
  (let ((real-zero (q1357684-real-zero ctx))
        (real-one (q1357684-real-one ctx))
        (zero (q1357684-scalar-zero ctx))
        (one (q1357684-scalar-one ctx))
        (i (q1357684-imaginary-unit ctx)))
    (and
     (booleanp (q1357684-complexp ctx))
     (q1357684-real-field-p ctx)
     (q1357684-scalar-member-p ctx zero)
     (q1357684-scalar-member-p ctx one)
     (not (equal zero one))
     (q1357684-scalar-member-p ctx i)
     (equal (q1357684-of-real ctx real-zero) zero)
     (equal (q1357684-of-real ctx real-one) one)
     (equal (q1357684-real-part ctx zero) real-zero)
     (equal (q1357684-imag-part ctx zero) real-zero)
     (equal (q1357684-real-part ctx one) real-one)
     (equal (q1357684-imag-part ctx one) real-zero)
     (q1357684-scalar-field-laws-p ctx)
     (q1357684-real-embedding-laws-p ctx)
     (q1357684-scalar-coordinate-laws-p ctx)
     (if (q1357684-complexp ctx)
         (and
          (equal (q1357684-real-part ctx i) real-zero)
          (equal (q1357684-imag-part ctx i) real-one)
          (equal
           (q1357684-scalar-mul ctx i i)
           (q1357684-scalar-neg ctx one)))
       (equal i zero)))))

(defun q1357684-scalar-norm-square (ctx x)
  (q1357684-real-add
   ctx
   (q1357684-real-mul
    ctx
    (q1357684-real-part ctx x)
    (q1357684-real-part ctx x))
   (q1357684-real-mul
    ctx
    (q1357684-imag-part ctx x)
    (q1357684-imag-part ctx x))))

;; Inner-product spaces and their norm topology.

(defstub q1357684-vector-member-p (ctx x) t)
(defstub q1357684-vector-zero (ctx) t)
(defstub q1357684-vector-add (ctx x y) t)
(defstub q1357684-vector-neg (ctx x) t)
(defstub q1357684-vector-smul (ctx a x) t)
(defstub q1357684-inner (ctx x y) t)
(defstub q1357684-sequence-value (ctx sequence-tag n) t)

(defun q1357684-vector-sub (ctx x y)
  (q1357684-vector-add
   ctx x (q1357684-vector-neg ctx y)))

(defun q1357684-scalar-sub (ctx x y)
  (q1357684-scalar-add
   ctx x (q1357684-scalar-neg ctx y)))

(defun q1357684-vector-norm-square (ctx x)
  (q1357684-real-part
   ctx (q1357684-inner ctx x x)))

(defun q1357684-vector-distance-lt-p
    (ctx x y epsilon)
  (q1357684-real-lt
   ctx
   (q1357684-vector-norm-square
    ctx (q1357684-vector-sub ctx x y))
   (q1357684-real-mul ctx epsilon epsilon)))

(defun q1357684-scalar-distance-lt-p
    (ctx x y epsilon)
  (q1357684-real-lt
   ctx
   (q1357684-scalar-norm-square
    ctx (q1357684-scalar-sub ctx x y))
   (q1357684-real-mul ctx epsilon epsilon)))

(defun-sk q1357684-vector-space-laws-p (ctx)
  (forall (a b x y z)
    (implies
     (and
      (q1357684-scalar-member-p ctx a)
      (q1357684-scalar-member-p ctx b)
      (q1357684-vector-member-p ctx x)
      (q1357684-vector-member-p ctx y)
      (q1357684-vector-member-p ctx z))
     (let ((zero (q1357684-vector-zero ctx))
           (one (q1357684-scalar-one ctx)))
       (and
        (q1357684-vector-member-p
         ctx (q1357684-vector-add ctx x y))
        (q1357684-vector-member-p
         ctx (q1357684-vector-neg ctx x))
        (q1357684-vector-member-p
         ctx (q1357684-vector-smul ctx a x))
        (equal
         (q1357684-vector-add
          ctx (q1357684-vector-add ctx x y) z)
         (q1357684-vector-add
          ctx x (q1357684-vector-add ctx y z)))
        (equal
         (q1357684-vector-add ctx x y)
         (q1357684-vector-add ctx y x))
        (equal (q1357684-vector-add ctx x zero) x)
        (equal
         (q1357684-vector-add
          ctx x (q1357684-vector-neg ctx x))
         zero)
        (equal
         (q1357684-vector-smul ctx one x) x)
        (equal
         (q1357684-vector-smul
          ctx (q1357684-scalar-mul ctx a b) x)
         (q1357684-vector-smul
          ctx a (q1357684-vector-smul ctx b x)))
        (equal
         (q1357684-vector-smul
          ctx (q1357684-scalar-add ctx a b) x)
         (q1357684-vector-add
          ctx
          (q1357684-vector-smul ctx a x)
          (q1357684-vector-smul ctx b x)))
        (equal
         (q1357684-vector-smul
          ctx a (q1357684-vector-add ctx x y))
         (q1357684-vector-add
          ctx
          (q1357684-vector-smul ctx a x)
          (q1357684-vector-smul ctx a y))))))))

(defun-sk q1357684-inner-product-laws-p (ctx)
  (forall (a x y z)
    (implies
     (and
      (q1357684-scalar-member-p ctx a)
      (q1357684-vector-member-p ctx x)
      (q1357684-vector-member-p ctx y)
      (q1357684-vector-member-p ctx z))
     (let ((inner-xy (q1357684-inner ctx x y))
           (inner-xx (q1357684-inner ctx x x))
           (real-zero (q1357684-real-zero ctx))
           (scalar-zero (q1357684-scalar-zero ctx))
           (vector-zero (q1357684-vector-zero ctx)))
       (and
        (q1357684-scalar-member-p ctx inner-xy)
        (equal
         (q1357684-inner
          ctx x (q1357684-vector-add ctx y z))
         (q1357684-scalar-add
          ctx inner-xy (q1357684-inner ctx x z)))
        (equal
         (q1357684-inner
          ctx x (q1357684-vector-smul ctx a y))
         (q1357684-scalar-mul ctx a inner-xy))
        (equal
         (q1357684-inner ctx y x)
         (q1357684-star ctx inner-xy))
        (equal
         (q1357684-imag-part ctx inner-xx)
         real-zero)
        (q1357684-real-le-p
         ctx real-zero
         (q1357684-real-part ctx inner-xx))
        (iff
         (equal inner-xx scalar-zero)
         (equal x vector-zero)))))))

(defun-sk q1357684-sequence-values-p (ctx sequence-tag)
  (forall (n)
    (implies
     (natp n)
     (q1357684-vector-member-p
      ctx
      (q1357684-sequence-value
       ctx sequence-tag n)))))

(defun-sk q1357684-cauchy-tail-p
    (ctx sequence-tag epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (q1357684-vector-distance-lt-p
      ctx
      (q1357684-sequence-value
       ctx sequence-tag m)
      (q1357684-sequence-value
       ctx sequence-tag n)
      epsilon))))

(defun-sk q1357684-cauchy-cutoff-exists-p
    (ctx sequence-tag epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1357684-cauchy-tail-p
      ctx sequence-tag epsilon cutoff))))

(defun-sk q1357684-cauchy-p (ctx sequence-tag)
  (forall (epsilon)
    (implies
     (q1357684-positive-real-p ctx epsilon)
     (q1357684-cauchy-cutoff-exists-p
      ctx sequence-tag epsilon))))

(defun-sk q1357684-convergence-tail-p
    (ctx sequence-tag limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q1357684-vector-distance-lt-p
      ctx
      (q1357684-sequence-value
       ctx sequence-tag n)
      limit
      epsilon))))

(defun-sk q1357684-convergence-cutoff-exists-p
    (ctx sequence-tag limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1357684-convergence-tail-p
      ctx sequence-tag limit epsilon cutoff))))

(defun-sk q1357684-converges-p
    (ctx sequence-tag limit)
  (forall (epsilon)
    (implies
     (q1357684-positive-real-p ctx epsilon)
     (q1357684-convergence-cutoff-exists-p
      ctx sequence-tag limit epsilon))))

(defun-sk q1357684-limit-exists-p
    (ctx sequence-tag)
  (exists (limit)
    (and
     (q1357684-vector-member-p ctx limit)
     (q1357684-converges-p
      ctx sequence-tag limit))))

(defun-sk q1357684-complete-space-p (ctx)
  (forall (sequence-tag)
    (implies
     (and
      (q1357684-sequence-values-p
       ctx sequence-tag)
      (q1357684-cauchy-p
       ctx sequence-tag))
     (q1357684-limit-exists-p
      ctx sequence-tag))))

(defun q1357684-hilbert-space-p (ctx)
  (and
   (q1357684-vector-member-p
    ctx (q1357684-vector-zero ctx))
   (q1357684-vector-space-laws-p ctx)
   (q1357684-inner-product-laws-p ctx)
   (q1357684-complete-space-p ctx)))

;; Strong-dual elements are arbitrary functional tags whose applications are
;; scalar-valued, linear, and continuous in the norm topology above.

(defstub q1357684-functional-value
  (ctx functional-tag vector)
  t)

(defun-sk q1357684-linear-functional-laws-p
    (ctx functional-tag)
  (forall (a x y)
    (implies
     (and
      (q1357684-scalar-member-p ctx a)
      (q1357684-vector-member-p ctx x)
      (q1357684-vector-member-p ctx y))
     (and
      (q1357684-scalar-member-p
       ctx
       (q1357684-functional-value
        ctx functional-tag x))
      (equal
       (q1357684-functional-value
        ctx functional-tag
        (q1357684-vector-add ctx x y))
       (q1357684-scalar-add
        ctx
        (q1357684-functional-value
         ctx functional-tag x)
        (q1357684-functional-value
         ctx functional-tag y)))
      (equal
       (q1357684-functional-value
        ctx functional-tag
        (q1357684-vector-smul ctx a x))
       (q1357684-scalar-mul
        ctx a
        (q1357684-functional-value
         ctx functional-tag x)))))))

(defun-sk q1357684-functional-neighborhood-p
    (ctx functional-tag x epsilon delta)
  (forall (y)
    (implies
     (and
      (q1357684-vector-member-p ctx y)
      (q1357684-vector-distance-lt-p
       ctx y x delta))
     (q1357684-scalar-distance-lt-p
      ctx
      (q1357684-functional-value
       ctx functional-tag y)
      (q1357684-functional-value
       ctx functional-tag x)
      epsilon))))

(defun-sk q1357684-functional-radius-exists-p
    (ctx functional-tag x epsilon)
  (exists (delta)
    (and
     (q1357684-positive-real-p ctx delta)
     (q1357684-functional-neighborhood-p
      ctx functional-tag x epsilon delta))))

(defun-sk q1357684-continuous-functional-p
    (ctx functional-tag)
  (forall (x epsilon)
    (implies
     (and
      (q1357684-vector-member-p ctx x)
      (q1357684-positive-real-p ctx epsilon))
     (q1357684-functional-radius-exists-p
      ctx functional-tag x epsilon))))

(defun q1357684-continuous-linear-functional-p
    (ctx functional-tag)
  (and
   (q1357684-linear-functional-laws-p
    ctx functional-tag)
   (q1357684-continuous-functional-p
    ctx functional-tag)))

;; The canonical map sends v to the functional y |-> <v,y>. The conclusion
;; states its surjectivity and uniqueness, which is equivalent to the
;; conjugate-linear isometric equivalence InnerProductSpace.toDual.

(defun-sk q1357684-represents-p
    (ctx functional-tag vector)
  (forall (y)
    (implies
     (q1357684-vector-member-p ctx y)
     (equal
      (q1357684-functional-value
       ctx functional-tag y)
      (q1357684-inner ctx vector y)))))

(defun-sk q1357684-representative-unique-p
    (ctx functional-tag vector)
  (forall (other)
    (implies
     (and
      (q1357684-vector-member-p ctx other)
      (q1357684-represents-p
       ctx functional-tag other))
     (equal other vector))))

(defun-sk q1357684-unique-representative-exists-p
    (ctx functional-tag)
  (exists (vector)
    (and
     (q1357684-vector-member-p ctx vector)
     (q1357684-represents-p
      ctx functional-tag vector)
     (q1357684-representative-unique-p
      ctx functional-tag vector))))

(defun-sk q1357684-all-functionals-represented-p (ctx)
  (forall (functional-tag)
    (implies
     (q1357684-continuous-linear-functional-p
      ctx functional-tag)
     (q1357684-unique-representative-exists-p
      ctx functional-tag))))

(defun q1357684-riesz-context-p (ctx)
  (and
   (q1357684-rclike-field-p ctx)
   (q1357684-hilbert-space-p ctx)))

(defun-sk thousand-theorems-q1357684-riesz-representation-theorem-statement ()
  (forall (ctx)
    (implies
     (q1357684-riesz-context-p ctx)
     (q1357684-all-functionals-represented-p ctx))))

(value-triple :itpeval-statement-checked)
:q
