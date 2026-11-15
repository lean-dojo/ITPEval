;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_a4:
;; integer combinations of the twelve regular-icosahedron vertex vectors are
;; dense in three-dimensional Euclidean space. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These unconstrained functions are arbitrary rational Cauchy presentations
;; of the three target coordinates and the positive tolerance. All properties
;; used below are explicit hypotheses of the statement predicate.
(defstub putnam-2023-a4-w-x-approx (precision) t)
(defstub putnam-2023-a4-w-y-approx (precision) t)
(defstub putnam-2023-a4-w-z-approx (precision) t)
(defstub putnam-2023-a4-epsilon-approx (precision) t)

(defun putnam-2023-a4-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

;; A regular name q satisfies |q(p)-q(r)| <= p+r. It therefore determines a
;; unique real x with |q(p)-x| <= p, and every real has such a rational name.
(defun-sk putnam-2023-a4-regular-cauchy-inputs-p ()
  (forall (precision eta)
    (implies
     (and
      (putnam-2023-a4-positive-rational-p precision)
      (putnam-2023-a4-positive-rational-p eta))
     (and
      (rationalp
       (putnam-2023-a4-w-x-approx precision))
      (rationalp
       (putnam-2023-a4-w-x-approx eta))
      (rationalp
       (putnam-2023-a4-w-y-approx precision))
      (rationalp
       (putnam-2023-a4-w-y-approx eta))
      (rationalp
       (putnam-2023-a4-w-z-approx precision))
      (rationalp
       (putnam-2023-a4-w-z-approx eta))
      (rationalp
       (putnam-2023-a4-epsilon-approx precision))
      (rationalp
       (putnam-2023-a4-epsilon-approx eta))
      (<=
       (abs
        (-
         (putnam-2023-a4-w-x-approx precision)
         (putnam-2023-a4-w-x-approx eta)))
       (+ precision eta))
      (<=
       (abs
        (-
         (putnam-2023-a4-w-y-approx precision)
         (putnam-2023-a4-w-y-approx eta)))
       (+ precision eta))
      (<=
       (abs
        (-
         (putnam-2023-a4-w-z-approx precision)
         (putnam-2023-a4-w-z-approx eta)))
       (+ precision eta))
      (<=
       (abs
        (-
         (putnam-2023-a4-epsilon-approx precision)
         (putnam-2023-a4-epsilon-approx eta)))
       (+ precision eta))))))

;; The limit of the epsilon name is positive exactly when it has a positive
;; rational lower margin of this form.
(defun-sk putnam-2023-a4-epsilon-margin-p (lower)
  (forall (precision)
    (implies
     (putnam-2023-a4-positive-rational-p precision)
     (<=
      lower
      (+
       (putnam-2023-a4-epsilon-approx precision)
       precision)))))

(defun-sk putnam-2023-a4-positive-epsilon-p ()
  (exists (lower)
    (and
     (putnam-2023-a4-positive-rational-p lower)
     (putnam-2023-a4-epsilon-margin-p lower))))

;; A pair (r s) denotes the exact real number r+s*sqrt(5).
(defun putnam-2023-a4-qroot5-rational (value)
  (list value 0))

(defun putnam-2023-a4-qroot5-add (left right)
  (list
   (+ (car left) (car right))
   (+ (cadr left) (cadr right))))

(defun putnam-2023-a4-qroot5-negate (value)
  (list
   (- (car value))
   (- (cadr value))))

(defun putnam-2023-a4-qroot5-subtract (left right)
  (putnam-2023-a4-qroot5-add
   left
   (putnam-2023-a4-qroot5-negate right)))

(defun putnam-2023-a4-qroot5-multiply (left right)
  (list
   (+
    (* (car left) (car right))
    (* 5 (cadr left) (cadr right)))
   (+
    (* (car left) (cadr right))
    (* (cadr left) (car right)))))

(defun putnam-2023-a4-qroot5-square (value)
  (putnam-2023-a4-qroot5-multiply value value))

;; For rational r and positive rational s, decide the sign of r+s*sqrt(5)
;; by comparing r^2 with 5*s^2.
(defun putnam-2023-a4-qroot5-sign-positive-root
    (rational-part root-part)
  (cond
   ((<= 0 rational-part) 1)
   ((<
     (* rational-part rational-part)
     (* 5 root-part root-part))
    1)
   ((<
     (* 5 root-part root-part)
     (* rational-part rational-part))
    -1)
   (t 0)))

(defun putnam-2023-a4-qroot5-sign (value)
  (let ((rational-part (car value))
        (root-part (cadr value)))
    (cond
     ((equal root-part 0)
      (cond
       ((< rational-part 0) -1)
       ((< 0 rational-part) 1)
       (t 0)))
     ((< 0 root-part)
      (putnam-2023-a4-qroot5-sign-positive-root
       rational-part root-part))
     (t
      (-
       (putnam-2023-a4-qroot5-sign-positive-root
        (- rational-part)
        (- root-part)))))))

(defun putnam-2023-a4-phi-affine
    (constant coefficient)
  ;; constant + coefficient*phi, where phi=(1+sqrt(5))/2.
  (list
   (+ constant (/ coefficient 2))
   (/ coefficient 2)))

(defun putnam-2023-a4-integer-prefix-p (values count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (consp values)
     (integerp (car values))
     (putnam-2023-a4-integer-prefix-p
      (cdr values)
      (- count 1)))))

;; For the displayed unnormalized vertices u_i, these six integer expressions
;; are the constant and phi coefficients of sum_i a_i*u_i.
(defun putnam-2023-a4-coefficient-x-constant (witness)
  (+
   (nth 0 witness)
   (- (nth 1 witness))
   (nth 2 witness)
   (- (nth 3 witness))))

(defun putnam-2023-a4-coefficient-x-phi (witness)
  (+
   (nth 4 witness)
   (nth 5 witness)
   (- (nth 6 witness))
   (- (nth 7 witness))))

(defun putnam-2023-a4-coefficient-y-constant (witness)
  (+
   (nth 8 witness)
   (- (nth 9 witness))
   (nth 10 witness)
   (- (nth 11 witness))))

(defun putnam-2023-a4-coefficient-y-phi (witness)
  (+
   (nth 0 witness)
   (nth 1 witness)
   (- (nth 2 witness))
   (- (nth 3 witness))))

(defun putnam-2023-a4-coefficient-z-constant (witness)
  (+
   (nth 4 witness)
   (- (nth 5 witness))
   (nth 6 witness)
   (- (nth 7 witness))))

(defun putnam-2023-a4-coefficient-z-phi (witness)
  (+
   (nth 8 witness)
   (nth 9 witness)
   (- (nth 10 witness))
   (- (nth 11 witness))))

(defun putnam-2023-a4-coordinate-error
    (constant coefficient target-sample)
  (putnam-2023-a4-qroot5-subtract
   (putnam-2023-a4-phi-affine
    constant coefficient)
   (putnam-2023-a4-qroot5-rational
    target-sample)))

(defun putnam-2023-a4-squared-gap
    (epsilon-sample error-x error-y error-z)
  (putnam-2023-a4-qroot5-subtract
   (putnam-2023-a4-qroot5-rational
    (* epsilon-sample epsilon-sample))
   (putnam-2023-a4-qroot5-add
    (putnam-2023-a4-qroot5-square error-x)
    (putnam-2023-a4-qroot5-add
     (putnam-2023-a4-qroot5-square error-y)
     (putnam-2023-a4-qroot5-square error-z)))))

;; The sampled squared gap converges to
;; epsilon^2-||sum_i a_i*u_i-w||^2. Requiring it to exceed one fixed positive
;; rational margin at every sufficiently fine precision is therefore exactly
;; the strict Euclidean norm inequality.
(defun-sk putnam-2023-a4-approximation-tail-p
    (witness cutoff margin)
  (forall (precision)
    (implies
     (and
      (putnam-2023-a4-positive-rational-p precision)
      (< precision cutoff))
     (let* ((x-sample
             (putnam-2023-a4-w-x-approx precision))
            (y-sample
             (putnam-2023-a4-w-y-approx precision))
            (z-sample
             (putnam-2023-a4-w-z-approx precision))
            (epsilon-sample
             (putnam-2023-a4-epsilon-approx precision))
            (error-x
             (putnam-2023-a4-coordinate-error
              (putnam-2023-a4-coefficient-x-constant witness)
              (putnam-2023-a4-coefficient-x-phi witness)
              x-sample))
            (error-y
             (putnam-2023-a4-coordinate-error
              (putnam-2023-a4-coefficient-y-constant witness)
              (putnam-2023-a4-coefficient-y-phi witness)
              y-sample))
            (error-z
             (putnam-2023-a4-coordinate-error
              (putnam-2023-a4-coefficient-z-constant witness)
              (putnam-2023-a4-coefficient-z-phi witness)
              z-sample))
            (gap
             (putnam-2023-a4-squared-gap
              epsilon-sample error-x error-y error-z)))
       (and
        (rationalp x-sample)
        (rationalp y-sample)
        (rationalp z-sample)
        (rationalp epsilon-sample)
        (equal
         (putnam-2023-a4-qroot5-sign
          (putnam-2023-a4-qroot5-subtract
           gap
           (putnam-2023-a4-qroot5-rational margin)))
         1))))))

(defun putnam-2023-a4-approximation-witness-p
    (witness cutoff margin)
  (and
   (true-listp witness)
   (equal (len witness) 12)
   (putnam-2023-a4-integer-prefix-p witness 12)
   (putnam-2023-a4-positive-rational-p cutoff)
   (putnam-2023-a4-positive-rational-p margin)
   (putnam-2023-a4-approximation-tail-p
    witness cutoff margin)))

(defun-sk putnam-2023-a4-approximation-exists-p ()
  (exists (witness cutoff margin)
    (putnam-2023-a4-approximation-witness-p
     witness cutoff margin)))

;; If g(v_i)=u_i/s for the source isometry and positive normalization s, then
;; the source inequality is equivalent to
;; ||sum_i a_i*u_i-s*g(w)|| < s*epsilon. Conversely, choose v_i=u_i/s and the
;; identity isometry. Thus the canonical unnormalized density predicate below
;; is bidirectionally equivalent to the quantified source statement.
(defun putnambench-putnam-2023-a4-statement ()
  (implies
   (and
    (putnam-2023-a4-regular-cauchy-inputs-p)
    (putnam-2023-a4-positive-epsilon-p))
   (putnam-2023-a4-approximation-exists-p)))

(value-triple :itpeval-statement-checked)
:q
