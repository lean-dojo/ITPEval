;; Statement-only formalization of thousand-theorems corpus artifact Q1068085,
;; "Closed graph theorem": a linear map between Banach spaces over an arbitrary
;; nontrivially normed field is continuous when its graph is closed. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces present arbitrary carriers and operations. Tame
;; APPLY$ function objects directly represent arbitrary sequences and linear
;; maps. Norms are represented by rounded rational upper cuts:
;; NORM-LT(type,x,q) means ||x|| < q. Such cuts represent genuine finite
;; nonnegative real values, not rational-valued approximations.
;;
;; Closedness of the graph and continuity are expressed sequentially. Normed
;; spaces are metrizable, so these formulations are bidirectionally equivalent
;; to the source notions. Every quantifier and witness below is introduced
;; directly by DEFUN-SK.

(defstub q1068085-member-p (carrier-type value) t)
(defstub q1068085-zero (carrier-type) t)
(defstub q1068085-one (carrier-type) t)
(defstub q1068085-add (carrier-type left right) t)
(defstub q1068085-multiply (carrier-type left right) t)
(defstub q1068085-negate (carrier-type value) t)
(defstub q1068085-inverse (carrier-type value) t)
(defstub q1068085-smul
  (field-type vector-type scalar vector)
  t)
(defstub q1068085-norm-lt-p
  (carrier-type value rational-bound)
  t)

(defun q1068085-sequence-value (sequence index)
  (apply$ sequence (list index)))

(defun q1068085-map-value (mapping value)
  (apply$ mapping (list value)))

(defun q1068085-positive-rational-p (q)
  (and (rationalp q) (< 0 q)))

(defun q1068085-subtract (carrier-type left right)
  (q1068085-add
   carrier-type
   left
   (q1068085-negate carrier-type right)))

(defun q1068085-norm-difference-lt-p
    (carrier-type left right epsilon)
  (q1068085-norm-lt-p
   carrier-type
   (q1068085-subtract carrier-type left right)
   epsilon))

(defun-sk q1068085-norm-finite-p
    (carrier-type value)
  (exists (q)
    (and
     (q1068085-positive-rational-p q)
     (q1068085-norm-lt-p carrier-type value q))))

(defun-sk q1068085-norm-positive-p
    (carrier-type value)
  (exists (q)
    (and
     (q1068085-positive-rational-p q)
     (not
      (q1068085-norm-lt-p
       carrier-type value q)))))

(defun-sk q1068085-norm-rounded-p
    (carrier-type value q)
  (exists (r)
    (and
     (q1068085-positive-rational-p r)
     (rationalp q)
     (< r q)
     (q1068085-norm-lt-p
      carrier-type value r))))

(defun-sk q1068085-norm-cut-laws-p
    (carrier-type)
  (forall (x q r)
    (implies
     (q1068085-member-p carrier-type x)
     (and
      (implies
       (q1068085-norm-lt-p carrier-type x q)
       (q1068085-positive-rational-p q))
      (implies
       (and
        (q1068085-norm-lt-p carrier-type x q)
        (rationalp r)
        (< q r))
       (q1068085-norm-lt-p carrier-type x r))
      (implies
       (q1068085-norm-lt-p carrier-type x q)
       (q1068085-norm-rounded-p
        carrier-type x q))
      (q1068085-norm-finite-p carrier-type x)
      (implies
       (equal x (q1068085-zero carrier-type))
       (iff
        (q1068085-norm-lt-p carrier-type x q)
        (q1068085-positive-rational-p q)))
      (implies
       (not
        (equal x (q1068085-zero carrier-type)))
       (q1068085-norm-positive-p
        carrier-type x))))))

(defun-sk q1068085-normed-add-comm-group-laws-p
    (carrier-type)
  (forall (x y z q r)
    (implies
     (and
      (q1068085-member-p carrier-type x)
      (q1068085-member-p carrier-type y)
      (q1068085-member-p carrier-type z))
     (and
      (q1068085-member-p
       carrier-type
       (q1068085-add carrier-type x y))
      (q1068085-member-p
       carrier-type
       (q1068085-negate carrier-type x))
      (equal
       (q1068085-add
        carrier-type
        (q1068085-add carrier-type x y)
        z)
       (q1068085-add
        carrier-type
        x
        (q1068085-add carrier-type y z)))
      (equal
       (q1068085-add carrier-type x y)
       (q1068085-add carrier-type y x))
      (equal
       (q1068085-add
        carrier-type
        x
        (q1068085-zero carrier-type))
       x)
      (equal
       (q1068085-add
        carrier-type
        x
        (q1068085-negate carrier-type x))
       (q1068085-zero carrier-type))
      (iff
       (q1068085-norm-lt-p
        carrier-type
        (q1068085-negate carrier-type x)
        q)
       (q1068085-norm-lt-p
        carrier-type x q))
      (implies
       (and
        (q1068085-positive-rational-p q)
        (q1068085-positive-rational-p r)
        (q1068085-norm-lt-p
         carrier-type x q)
        (q1068085-norm-lt-p
         carrier-type y r))
       (q1068085-norm-lt-p
        carrier-type
        (q1068085-add carrier-type x y)
        (+ q r)))))))

(defun q1068085-normed-add-comm-group-p
    (carrier-type)
  (and
   (q1068085-member-p
    carrier-type
    (q1068085-zero carrier-type))
   (q1068085-norm-cut-laws-p carrier-type)
   (q1068085-normed-add-comm-group-laws-p
    carrier-type)))

(defun-sk q1068085-product-norm-lt-p
    (field-type x y q)
  (exists (r s)
    (and
     (q1068085-positive-rational-p q)
     (q1068085-positive-rational-p r)
     (q1068085-positive-rational-p s)
     (q1068085-norm-lt-p field-type x r)
     (q1068085-norm-lt-p field-type y s)
     (< (* r s) q))))

(defun-sk q1068085-field-laws-p
    (field-type)
  (forall (x y z)
    (implies
     (and
      (q1068085-member-p field-type x)
      (q1068085-member-p field-type y)
      (q1068085-member-p field-type z))
     (and
      (q1068085-member-p
       field-type
       (q1068085-multiply field-type x y))
      (q1068085-member-p
       field-type
       (q1068085-inverse field-type x))
      (equal
       (q1068085-multiply
        field-type
        (q1068085-multiply field-type x y)
        z)
       (q1068085-multiply
        field-type
        x
        (q1068085-multiply field-type y z)))
      (equal
       (q1068085-multiply field-type x y)
       (q1068085-multiply field-type y x))
      (equal
       (q1068085-multiply
        field-type
        x
        (q1068085-one field-type))
       x)
      (equal
       (q1068085-inverse
        field-type
        (q1068085-zero field-type))
       (q1068085-zero field-type))
      (implies
       (not
        (equal x (q1068085-zero field-type)))
       (equal
        (q1068085-multiply
         field-type
         x
         (q1068085-inverse field-type x))
        (q1068085-one field-type)))
      (equal
       (q1068085-multiply
        field-type
        x
        (q1068085-add field-type y z))
       (q1068085-add
        field-type
        (q1068085-multiply field-type x y)
        (q1068085-multiply field-type x z)))))))

(defun-sk q1068085-field-norm-laws-p
    (field-type)
  (forall (x y q)
    (implies
     (and
      (q1068085-member-p field-type x)
      (q1068085-member-p field-type y))
     (iff
      (q1068085-norm-lt-p
       field-type
       (q1068085-multiply field-type x y)
       q)
      (q1068085-product-norm-lt-p
       field-type x y q)))))

(defun-sk q1068085-large-norm-element-exists-p
    (field-type)
  (exists (x q)
    (and
     (q1068085-member-p field-type x)
     (rationalp q)
     (< 1 q)
     (not
      (q1068085-norm-lt-p
       field-type x q)))))

(defun q1068085-nontrivially-normed-field-p
    (field-type)
  (and
   (q1068085-normed-add-comm-group-p
    field-type)
   (q1068085-member-p
    field-type
    (q1068085-one field-type))
   (not
    (equal
     (q1068085-zero field-type)
     (q1068085-one field-type)))
   (q1068085-field-laws-p field-type)
   (q1068085-field-norm-laws-p field-type)
   (q1068085-large-norm-element-exists-p
    field-type)))

(defun-sk q1068085-scaled-norm-lt-p
    (field-type vector-type scalar vector q)
  (exists (r s)
    (and
     (q1068085-positive-rational-p q)
     (q1068085-positive-rational-p r)
     (q1068085-positive-rational-p s)
     (q1068085-norm-lt-p field-type scalar r)
     (q1068085-norm-lt-p vector-type vector s)
     (< (* r s) q))))

(defun-sk q1068085-normed-space-laws-p
    (field-type vector-type)
  (forall (a b x y q)
    (implies
     (and
      (q1068085-member-p field-type a)
      (q1068085-member-p field-type b)
      (q1068085-member-p vector-type x)
      (q1068085-member-p vector-type y))
     (and
      (q1068085-member-p
       vector-type
       (q1068085-smul
        field-type vector-type a x))
      (equal
       (q1068085-smul
        field-type
        vector-type
        (q1068085-one field-type)
        x)
       x)
      (equal
       (q1068085-smul
        field-type
        vector-type
        (q1068085-multiply field-type a b)
        x)
       (q1068085-smul
        field-type
        vector-type
        a
        (q1068085-smul
         field-type vector-type b x)))
      (equal
       (q1068085-smul
        field-type
        vector-type
        (q1068085-add field-type a b)
        x)
       (q1068085-add
        vector-type
        (q1068085-smul
         field-type vector-type a x)
        (q1068085-smul
         field-type vector-type b x)))
      (equal
       (q1068085-smul
        field-type
        vector-type
        a
        (q1068085-add vector-type x y))
       (q1068085-add
        vector-type
        (q1068085-smul
         field-type vector-type a x)
        (q1068085-smul
         field-type vector-type a y)))
      (iff
       (q1068085-norm-lt-p
        vector-type
        (q1068085-smul
         field-type vector-type a x)
        q)
       (q1068085-scaled-norm-lt-p
        field-type vector-type a x q))))))

(defun q1068085-normed-space-p
    (field-type vector-type)
  (and
   (q1068085-normed-add-comm-group-p
    vector-type)
   (q1068085-normed-space-laws-p
    field-type vector-type)))

(defun-sk q1068085-sequence-valid-p
    (carrier-type sequence)
  (forall (n)
    (and
     (tamep-functionp sequence)
     (implies
      (natp n)
      (q1068085-member-p
       carrier-type
       (q1068085-sequence-value sequence n))))))

(defun-sk q1068085-cauchy-tail-p
    (carrier-type sequence epsilon n0)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp n0)
      (<= n0 m)
      (<= n0 n))
     (q1068085-norm-difference-lt-p
      carrier-type
      (q1068085-sequence-value sequence m)
      (q1068085-sequence-value sequence n)
      epsilon))))

(defun-sk q1068085-cauchy-epsilon-p
    (carrier-type sequence epsilon)
  (exists (n0)
    (and
     (natp n0)
     (q1068085-cauchy-tail-p
      carrier-type sequence epsilon n0))))

(defun-sk q1068085-cauchy-all-epsilon-p
    (carrier-type sequence)
  (forall (epsilon)
    (implies
     (q1068085-positive-rational-p epsilon)
     (q1068085-cauchy-epsilon-p
      carrier-type sequence epsilon))))

(defun q1068085-cauchy-p
    (carrier-type sequence)
  (and
   (q1068085-sequence-valid-p
    carrier-type sequence)
   (q1068085-cauchy-all-epsilon-p
    carrier-type sequence)))

(defun-sk q1068085-convergence-tail-p
    (carrier-type sequence limit epsilon n0)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp n0)
      (<= n0 n))
     (q1068085-norm-difference-lt-p
      carrier-type
      (q1068085-sequence-value sequence n)
      limit
      epsilon))))

(defun-sk q1068085-convergence-epsilon-p
    (carrier-type sequence limit epsilon)
  (exists (n0)
    (and
     (natp n0)
     (q1068085-convergence-tail-p
      carrier-type sequence limit epsilon n0))))

(defun-sk q1068085-convergence-all-epsilon-p
    (carrier-type sequence limit)
  (forall (epsilon)
    (implies
     (q1068085-positive-rational-p epsilon)
     (q1068085-convergence-epsilon-p
      carrier-type sequence limit epsilon))))

(defun q1068085-converges-p
    (carrier-type sequence limit)
  (and
   (q1068085-member-p carrier-type limit)
   (q1068085-sequence-valid-p
    carrier-type sequence)
   (q1068085-convergence-all-epsilon-p
    carrier-type sequence limit)))

(defun-sk q1068085-limit-exists-p
    (carrier-type sequence)
  (exists (limit)
    (q1068085-converges-p
     carrier-type sequence limit)))

(defun-sk q1068085-complete-space-p
    (carrier-type)
  (forall (sequence)
    (implies
     (q1068085-cauchy-p
      carrier-type sequence)
     (q1068085-limit-exists-p
      carrier-type sequence))))

(defun q1068085-banach-space-p
    (field-type vector-type)
  (and
   (q1068085-normed-space-p
    field-type vector-type)
   (q1068085-complete-space-p
    vector-type)))

(defun-sk q1068085-linear-map-p
    (field-type domain-type codomain-type mapping)
  (forall (a x y)
    (and
     (tamep-functionp mapping)
     (implies
      (and
       (q1068085-member-p field-type a)
       (q1068085-member-p domain-type x)
       (q1068085-member-p domain-type y))
      (and
       (q1068085-member-p
        codomain-type
        (q1068085-map-value mapping x))
       (equal
        (q1068085-map-value
         mapping
         (q1068085-add domain-type x y))
        (q1068085-add
         codomain-type
         (q1068085-map-value mapping x)
         (q1068085-map-value mapping y)))
       (equal
        (q1068085-map-value
         mapping
         (q1068085-smul
          field-type domain-type a x))
        (q1068085-smul
         field-type
         codomain-type
         a
         (q1068085-map-value mapping x))))))))

(defun-sk q1068085-mapped-convergence-tail-p
    (domain-type codomain-type mapping
     sequence limit epsilon n0)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp n0)
      (<= n0 n))
     (q1068085-norm-difference-lt-p
      codomain-type
      (q1068085-map-value
       mapping
       (q1068085-sequence-value sequence n))
      limit
      epsilon))))

(defun-sk q1068085-mapped-convergence-epsilon-p
    (domain-type codomain-type mapping
     sequence limit epsilon)
  (exists (n0)
    (and
     (natp n0)
     (q1068085-mapped-convergence-tail-p
      domain-type codomain-type mapping
      sequence limit epsilon n0))))

(defun-sk q1068085-mapped-convergence-all-epsilon-p
    (domain-type codomain-type mapping
     sequence limit)
  (forall (epsilon)
    (implies
     (q1068085-positive-rational-p epsilon)
     (q1068085-mapped-convergence-epsilon-p
      domain-type codomain-type mapping
      sequence limit epsilon))))

(defun q1068085-mapped-converges-p
    (domain-type codomain-type mapping
     sequence limit)
  (and
   (tamep-functionp mapping)
   (q1068085-member-p codomain-type limit)
   (q1068085-sequence-valid-p
    domain-type sequence)
   (q1068085-mapped-convergence-all-epsilon-p
    domain-type codomain-type mapping
    sequence limit)))

(defun-sk q1068085-closed-graph-p
    (domain-type codomain-type mapping)
  (forall (sequence x y)
    (implies
     (and
      (q1068085-converges-p
       domain-type sequence x)
      (q1068085-mapped-converges-p
       domain-type codomain-type mapping
       sequence y))
     (equal
      y
      (q1068085-map-value mapping x)))))

(defun-sk q1068085-continuous-p
    (domain-type codomain-type mapping)
  (forall (sequence x)
    (implies
     (q1068085-converges-p
      domain-type sequence x)
     (q1068085-mapped-converges-p
      domain-type
      codomain-type
      mapping
      sequence
      (q1068085-map-value mapping x)))))

(defun-sk
    thousand-theorems-q1068085-closed-graph-theorem-statement ()
  (forall (field-type domain-type codomain-type mapping)
    (implies
     (and
      (q1068085-nontrivially-normed-field-p
       field-type)
      (q1068085-banach-space-p
       field-type domain-type)
      (q1068085-banach-space-p
       field-type codomain-type)
      (q1068085-linear-map-p
       field-type domain-type codomain-type mapping)
      (q1068085-closed-graph-p
       domain-type codomain-type mapping))
     (q1068085-continuous-p
      domain-type codomain-type mapping))))

(value-triple :itpeval-statement-checked)
:q
