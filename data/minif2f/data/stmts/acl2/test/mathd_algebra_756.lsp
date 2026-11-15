;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_756:
;; for arbitrary real a and b, 2^a = 32 and a^b = 125 imply b^a = 243,
;; with real exponentiation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative symbols are arbitrary precision-indexed rational
;; approximations to a and b.  Pairwise regularity below is exactly the usual
;; rational regular-Cauchy presentation: every such name has a unique real
;; limit, and every classical real has such a name.  Hence this representation
;; has a concrete two-way correspondence with R and is not restricted to tame
;; APPLY$ functions, computable reals, rationals, or integers.
;;
;; The antecedent is inhabited: the constant interpretations A-APPROX = 5 and
;; B-APPROX = 3 are regular names and satisfy its two limit equations.
(defstub m756-a-approx (precision) t)
(defstub m756-b-approx (precision) t)

(defun m756-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun m756-real-approx (which precision)
  (cond
   ((equal which :a)
    (m756-a-approx precision))
   ((equal which :b)
    (m756-b-approx precision))
   ((equal which :two)
    2)
   (t 0)))

;; For positive rational precisions EPSILON and ETA, the returned values lie
;; within EPSILON+ETA.  Such a name determines one element of the Cauchy
;; completion of Q; conversely, density of Q supplies a regular name for every
;; real.  DEFSTUB makes the two names genuinely arbitrary function symbols.
(defun-sk m756-real-name-p (which)
  (forall (epsilon eta)
    (implies
     (and
      (m756-positive-rational-p epsilon)
      (m756-positive-rational-p eta))
     (let ((left (m756-real-approx which epsilon))
           (right (m756-real-approx which eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun m756-natural-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      1
    (* base
       (m756-natural-power base (- exponent 1)))))

;; Return a rational lower approximation to the positive DEGREE-th root of
;; RADICAND.  The search starts above the root and uses a grid of width
;; 1/SCALE, so its error is less than 1/SCALE.
(defun m756-root-lower-search
    (radicand degree scale candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (let ((value (/ candidate scale)))
      (if (<= (m756-natural-power value degree)
              radicand)
          value
        (m756-root-lower-search
         radicand degree scale (- candidate 1))))))

(defun m756-root-lower (radicand degree scale)
  (if (and
       (rationalp radicand)
       (< 0 radicand)
       (posp degree)
       (posp scale))
      (let* ((upper
              (if (< radicand 1)
                  1
                (ceiling radicand 1)))
             (candidate (* upper scale)))
        (m756-root-lower-search
         radicand degree scale candidate))
    0))

;; For positive rational BASE and rational EXPONENT = p/q, this is a lower
;; rational approximation to BASE^(p/q).  Negative p is handled by taking the
;; reciprocal before the positive q-th root.
(defun m756-rational-power-lower
    (base exponent scale)
  (if (and
       (rationalp base)
       (< 0 base)
       (rationalp exponent)
       (posp scale))
      (let* ((numerator (numerator exponent))
             (degree (denominator exponent))
             (radicand
              (if (< numerator 0)
                  (/ 1
                     (m756-natural-power
                      base (- numerator)))
                (m756-natural-power
                 base numerator))))
        (m756-root-lower radicand degree scale))
    0))

(defun m756-stage-precision (stage)
  (/ 1 (+ 1 (nfix stage))))

;; Sampling both regular names at precision 1/(stage+1), then evaluating the
;; exact rational exponent through principal positive roots, converges to
;; x^y = exp(y*log(x)) whenever x>0.  This is the common real-power semantics
;; of all ground-truth occurrences after their preceding equations establish
;; the bases as 2, 5, and 3.  No positivity or integrality guard is assumed:
;; deriving those facts remains part of the original proof obligation.
(defun m756-real-power-approx
    (base-which exponent-which stage)
  (let* ((precision (m756-stage-precision stage))
         (base
          (m756-real-approx base-which precision))
         (exponent
          (m756-real-approx exponent-which precision))
         (scale (+ 1 (nfix stage))))
    (m756-rational-power-lower
     base exponent scale)))

(defun-sk m756-real-power-tail-p
    (base-which exponent-which target epsilon cutoff)
  (forall (stage)
    (implies
     (and
      (natp stage)
      (<= cutoff stage))
     (<
      (abs
       (-
        (m756-real-power-approx
         base-which exponent-which stage)
        target))
      epsilon))))

(defun-sk m756-real-power-cutoff-exists-p
    (base-which exponent-which target epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (m756-real-power-tail-p
      base-which exponent-which
      target epsilon cutoff))))

;; Equality of the represented real power to TARGET is exact convergence, not
;; equality at a bounded precision or at one rational sample.
(defun-sk m756-real-power-equals-p
    (base-which exponent-which target)
  (forall (epsilon)
    (implies
     (m756-positive-rational-p epsilon)
     (m756-real-power-cutoff-exists-p
      base-which exponent-which
      target epsilon))))

(defun minif2f-mathd-algebra-756-statement ()
  (implies
   (and
    (m756-real-name-p :a)
    (m756-real-name-p :b)
    (m756-real-power-equals-p :two :a 32)
    (m756-real-power-equals-p :a :b 125))
   (m756-real-power-equals-p :b :a 243)))

(value-triple :itpeval-statement-checked)
:q
