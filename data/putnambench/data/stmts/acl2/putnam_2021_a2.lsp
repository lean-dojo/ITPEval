;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_a2:
;; the right-hand real-power limit defining g(x) for every positive real x
;; implies that g(x)/x tends to exp(1) as x tends to infinity. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Exact reals are regular Cauchy names with rational values.  A name a
;; represents the limit of a(n), with the displayed modulus.  DEFSTUB keeps
;; the source function g arbitrary; the statement explicitly requires that it
;; map real names to real names and respect equality of represented reals.

(defstub putnam-2021-a2-g (x) t)

(defun putnam-2021-a2-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun putnam-2021-a2-real-value (name index)
  (apply$ name (list index)))

(defun-sk putnam-2021-a2-rational-values-p (name)
  (forall (index)
    (implies
     (natp index)
     (rationalp
      (putnam-2021-a2-real-value name index)))))

(defun-sk putnam-2021-a2-regular-cauchy-p (name)
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (natp right-index))
     (<=
      (abs
       (-
        (putnam-2021-a2-real-value name left-index)
        (putnam-2021-a2-real-value name right-index)))
      (+
       (/ 1 (+ 1 left-index))
       (/ 1 (+ 1 right-index)))))))

(defun putnam-2021-a2-real-name-p (name)
  (and
   (tamep-functionp name)
   (putnam-2021-a2-rational-values-p name)
   (putnam-2021-a2-regular-cauchy-p name)))

(defun putnam-2021-a2-constant-name (value)
  (list 'lambda
        '(index)
        (list 'quote value)))

(defun putnam-2021-a2-zero-name ()
  (putnam-2021-a2-constant-name 0))

(defun putnam-2021-a2-one-name ()
  (putnam-2021-a2-constant-name 1))

;; Rational sequence expressions used below have their ordinary pointwise
;; meanings.  EXP uses the diagonal sequence of exponential-series prefixes.

(defun putnam-2021-a2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-2021-a2-factorial (- n 1)))))

(defun putnam-2021-a2-rational-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      1
    (* base
       (putnam-2021-a2-rational-power
        base (- exponent 1)))))

(defun putnam-2021-a2-exp-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+
       (putnam-2021-a2-exp-prefix x index)
       (/
        (putnam-2021-a2-rational-power x index)
        (putnam-2021-a2-factorial index))))))

(defun putnam-2021-a2-sequence-value
    (kind arguments index)
  (let ((left
         (putnam-2021-a2-real-value
          (car arguments) index)))
    (cond
     ((equal kind :identity)
      left)
     ((equal kind :add)
      (+ left
         (putnam-2021-a2-real-value
          (cadr arguments) index)))
     ((equal kind :subtract)
      (- left
         (putnam-2021-a2-real-value
          (cadr arguments) index)))
     ((equal kind :multiply)
      (* left
         (putnam-2021-a2-real-value
          (cadr arguments) index)))
     ((equal kind :reciprocal)
      (/ 1 left))
     ((equal kind :exp)
      (putnam-2021-a2-exp-prefix
       left (+ 1 (nfix index))))
     (t 0))))

(defun-sk putnam-2021-a2-sequence-tail-p
    (output kind arguments epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (abs
       (-
        (putnam-2021-a2-real-value output index)
        (putnam-2021-a2-sequence-value
         kind arguments index)))
      epsilon))))

(defun-sk putnam-2021-a2-sequence-cutoff-exists-p
    (output kind arguments epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2021-a2-sequence-tail-p
      output kind arguments epsilon cutoff))))

(defun-sk putnam-2021-a2-represents-sequence-p
    (output kind arguments)
  (forall (epsilon)
    (implies
     (putnam-2021-a2-positive-rational-p epsilon)
     (putnam-2021-a2-sequence-cutoff-exists-p
      output kind arguments epsilon))))

;; Exact equality and strict inequalities use the rational neighborhood basis
;; of the real topology, which is equivalent to quantifying over real radii.

(defun-sk putnam-2021-a2-distance-tail-p
    (left right margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (abs
       (-
        (putnam-2021-a2-real-value left index)
        (putnam-2021-a2-real-value right index)))
      margin))))

(defun-sk putnam-2021-a2-distance-below-p
    (left right epsilon)
  (exists (margin cutoff)
    (and
     (putnam-2021-a2-positive-rational-p margin)
     (< margin epsilon)
     (natp cutoff)
     (putnam-2021-a2-distance-tail-p
      left right margin cutoff))))

(defun-sk putnam-2021-a2-real-equal-p (left right)
  (forall (epsilon)
    (implies
     (putnam-2021-a2-positive-rational-p epsilon)
     (putnam-2021-a2-distance-below-p
      left right epsilon))))

(defun-sk putnam-2021-a2-positive-tail-p
    (name margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (< margin
        (putnam-2021-a2-real-value name index)))))

(defun-sk putnam-2021-a2-real-positive-p (name)
  (exists (margin cutoff)
    (and
     (putnam-2021-a2-positive-rational-p margin)
     (natp cutoff)
     (putnam-2021-a2-positive-tail-p
      name margin cutoff))))

(defun-sk putnam-2021-a2-below-rational-tail-p
    (name bound margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (putnam-2021-a2-real-value name index)
      (- bound margin)))))

(defun-sk putnam-2021-a2-below-rational-p
    (name bound)
  (exists (margin cutoff)
    (and
     (rationalp bound)
     (putnam-2021-a2-positive-rational-p margin)
     (natp cutoff)
     (putnam-2021-a2-below-rational-tail-p
      name bound margin cutoff))))

(defun-sk putnam-2021-a2-above-rational-tail-p
    (name bound margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (+ bound margin)
      (putnam-2021-a2-real-value name index)))))

(defun-sk putnam-2021-a2-above-rational-p
    (name bound)
  (exists (margin cutoff)
    (and
     (rationalp bound)
     (putnam-2021-a2-positive-rational-p margin)
     (natp cutoff)
     (putnam-2021-a2-above-rational-tail-p
      name bound margin cutoff))))

(defun putnam-2021-a2-add-p (left right output)
  (and
   (putnam-2021-a2-real-name-p left)
   (putnam-2021-a2-real-name-p right)
   (putnam-2021-a2-real-name-p output)
   (putnam-2021-a2-represents-sequence-p
    output :add (list left right))))

(defun putnam-2021-a2-subtract-p (left right output)
  (and
   (putnam-2021-a2-real-name-p left)
   (putnam-2021-a2-real-name-p right)
   (putnam-2021-a2-real-name-p output)
   (putnam-2021-a2-represents-sequence-p
    output :subtract (list left right))))

(defun putnam-2021-a2-multiply-p (left right output)
  (and
   (putnam-2021-a2-real-name-p left)
   (putnam-2021-a2-real-name-p right)
   (putnam-2021-a2-real-name-p output)
   (putnam-2021-a2-represents-sequence-p
    output :multiply (list left right))))

(defun putnam-2021-a2-reciprocal-p (input output)
  (and
   (putnam-2021-a2-real-name-p input)
   (putnam-2021-a2-real-name-p output)
   (not
    (putnam-2021-a2-real-equal-p
     input (putnam-2021-a2-zero-name)))
   (putnam-2021-a2-represents-sequence-p
    output :reciprocal (list input))))

(defun putnam-2021-a2-exp-p (input output)
  (and
   (putnam-2021-a2-real-name-p input)
   (putnam-2021-a2-real-name-p output)
   (putnam-2021-a2-represents-sequence-p
    output :exp (list input))))

;; For a positive base, base^exponent is exp(exponent*log(base)).  LOG is
;; represented without a new primitive: log(base) is the unique real whose
;; exponential is base.

(defun-sk putnam-2021-a2-positive-power-p
    (base exponent output)
  (exists (logarithm product)
    (and
     (putnam-2021-a2-real-name-p base)
     (putnam-2021-a2-real-positive-p base)
     (putnam-2021-a2-real-name-p exponent)
     (putnam-2021-a2-real-name-p output)
     (putnam-2021-a2-exp-p logarithm base)
     (putnam-2021-a2-multiply-p
      exponent logarithm product)
     (putnam-2021-a2-exp-p product output))))

(defun-sk putnam-2021-a2-expression-p
    (x r output)
  (exists
      (x-plus-one r-plus-one left-power right-power
                  difference reciprocal-r)
    (and
     (putnam-2021-a2-add-p
      x (putnam-2021-a2-one-name) x-plus-one)
     (putnam-2021-a2-add-p
      r (putnam-2021-a2-one-name) r-plus-one)
     (putnam-2021-a2-positive-power-p
      x-plus-one r-plus-one left-power)
     (putnam-2021-a2-positive-power-p
      x r-plus-one right-power)
     (putnam-2021-a2-subtract-p
      left-power right-power difference)
     (putnam-2021-a2-reciprocal-p
      r reciprocal-r)
     (putnam-2021-a2-positive-power-p
      difference reciprocal-r output))))

(defun-sk putnam-2021-a2-expression-exists-p (x r)
  (exists (output)
    (putnam-2021-a2-expression-p x r output)))

(defun-sk putnam-2021-a2-expression-close-p
    (x r epsilon)
  (forall (output)
    (implies
     (putnam-2021-a2-expression-p x r output)
     (putnam-2021-a2-distance-below-p
      output (putnam-2021-a2-g x) epsilon))))

(defun-sk putnam-2021-a2-inner-eventually-p
    (x epsilon delta)
  (forall (r)
    (implies
     (and
      (putnam-2021-a2-real-name-p r)
      (putnam-2021-a2-real-positive-p r)
      (putnam-2021-a2-below-rational-p r delta))
     (and
      (putnam-2021-a2-expression-exists-p x r)
      (putnam-2021-a2-expression-close-p
       x r epsilon)))))

(defun-sk putnam-2021-a2-inner-delta-exists-p
    (x epsilon)
  (exists (delta)
    (and
     (putnam-2021-a2-positive-rational-p delta)
     (putnam-2021-a2-inner-eventually-p
      x epsilon delta))))

(defun-sk putnam-2021-a2-inner-limit-p (x)
  (forall (epsilon)
    (implies
     (putnam-2021-a2-positive-rational-p epsilon)
     (putnam-2021-a2-inner-delta-exists-p
      x epsilon))))

(defun-sk putnam-2021-a2-g-values-p ()
  (forall (x)
    (implies
     (putnam-2021-a2-real-name-p x)
     (putnam-2021-a2-real-name-p
      (putnam-2021-a2-g x)))))

(defun-sk putnam-2021-a2-g-extensional-p ()
  (forall (x y)
    (implies
     (and
      (putnam-2021-a2-real-name-p x)
      (putnam-2021-a2-real-name-p y)
      (putnam-2021-a2-real-equal-p x y))
     (putnam-2021-a2-real-equal-p
      (putnam-2021-a2-g x)
      (putnam-2021-a2-g y)))))

(defun-sk putnam-2021-a2-hypothesis-p ()
  (forall (x)
    (implies
     (and
      (putnam-2021-a2-real-name-p x)
      (putnam-2021-a2-real-positive-p x))
     (putnam-2021-a2-inner-limit-p x))))

;; The quotient g(x)/x is evaluated directly on rational approximants.  Since
;; x is eventually bounded below by a positive cutoff, this diagonal quotient
;; converges to the exact real quotient.

(defun-sk putnam-2021-a2-quotient-tail-p
    (x limit margin index-cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= index-cutoff index))
     (<
      (abs
       (-
        (/
         (putnam-2021-a2-real-value
          (putnam-2021-a2-g x) index)
         (putnam-2021-a2-real-value x index))
        (putnam-2021-a2-real-value limit index)))
      margin))))

(defun-sk putnam-2021-a2-quotient-distance-below-p
    (x limit epsilon)
  (exists (margin index-cutoff)
    (and
     (putnam-2021-a2-positive-rational-p margin)
     (< margin epsilon)
     (natp index-cutoff)
     (putnam-2021-a2-quotient-tail-p
      x limit margin index-cutoff))))

(defun-sk putnam-2021-a2-outer-eventually-p
    (limit epsilon cutoff)
  (forall (x)
    (implies
     (and
      (putnam-2021-a2-real-name-p x)
      (putnam-2021-a2-above-rational-p x cutoff))
     (putnam-2021-a2-quotient-distance-below-p
      x limit epsilon))))

(defun-sk putnam-2021-a2-outer-cutoff-exists-p
    (limit epsilon)
  (exists (cutoff)
    (and
     (rationalp cutoff)
     (putnam-2021-a2-outer-eventually-p
      limit epsilon cutoff))))

(defun-sk putnam-2021-a2-conclusion-p (limit)
  (forall (epsilon)
    (implies
     (putnam-2021-a2-positive-rational-p epsilon)
     (putnam-2021-a2-outer-cutoff-exists-p
      limit epsilon))))

(defun-sk putnambench-putnam-2021-a2-statement ()
  (exists (exp-one)
    (and
     (putnam-2021-a2-exp-p
      (putnam-2021-a2-one-name) exp-one)
     (implies
      (and
       (putnam-2021-a2-g-values-p)
       (putnam-2021-a2-g-extensional-p)
       (putnam-2021-a2-hypothesis-p))
      (putnam-2021-a2-conclusion-p exp-one)))))

(value-triple :itpeval-statement-checked)
:q
