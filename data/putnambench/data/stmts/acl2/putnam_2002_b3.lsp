;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_b3:
;; the two-sided error bounds for (1-1/n)^n as an approximation to 1/e for
;; every integer n greater than one. This file contains no proof.

(in-package "ACL2")

(defun putnam-2002-b3-quoted (object)
  (list 'quote object))

(defun putnam-2002-b3-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2002-b3-and-terms (cdr terms))
       (putnam-2002-b3-quoted nil))
    (putnam-2002-b3-quoted t)))

(defun putnam-2002-b3-true-function ()
  (list 'lambda '(witness)
        (putnam-2002-b3-quoted t)))

;; (CAR LOOP$-IVARS) is an index j and (CAR LOOP$-GVARS) is a proposed finite
;; list of Taylor terms. This fully tame function checks term_0 = 1 and
;; term_j = term_(j-1)/j for every positive j.
(defun putnam-2002-b3-taylor-entry-function ()
  '(lambda (loop$-gvars loop$-ivars)
     (if (equal (car loop$-ivars) '0)
         (equal
          (nth (car loop$-ivars) (car loop$-gvars))
          '1)
       (equal
        (nth (car loop$-ivars) (car loop$-gvars))
        (binary-*
         (nth
          (binary-+ (car loop$-ivars) '-1)
          (car loop$-gvars))
         (unary-/ (car loop$-ivars)))))))

(defun putnam-2002-b3-singleton-index-function ()
  '(lambda (index)
     (cons index 'nil)))

(defun putnam-2002-b3-taylor-prefix-valid-term (terms)
  (let* ((range
          (list
           'from-to-by
           (putnam-2002-b3-quoted 0)
           (list
            'binary-+
            (list 'len terms)
            (putnam-2002-b3-quoted -1))
           (putnam-2002-b3-quoted 1)))
         (wrapped-range
          (list
           'collect$
           (putnam-2002-b3-quoted
            (putnam-2002-b3-singleton-index-function))
           range)))
    (list
     'always$+
     (putnam-2002-b3-quoted
      (putnam-2002-b3-taylor-entry-function))
     (list
      'cons
      terms
      (putnam-2002-b3-quoted nil))
     wrapped-range)))

(defun putnam-2002-b3-taylor-prefix-sum-term (terms)
  (list
   'sum$
   (putnam-2002-b3-quoted 'identity)
   terms))

;; The witness is the complete list 1/0!,...,1/k!. The tame recurrence check
;; makes its SUM$ value exactly the degree-k Taylor prefix. The function
;; differs from constant true exactly when a prefix exceeds THRESHOLD, so
;; NOT/FN-EQUAL keeps k and its finite certificate internal and expresses
;; THRESHOLD < exp(1).
(defun putnam-2002-b3-not-below-e-function (threshold)
  (let* ((witness 'witness)
         (qualification
          (putnam-2002-b3-and-terms
           (list
            (list 'true-listp witness)
            (list 'consp witness)
            (putnam-2002-b3-taylor-prefix-valid-term
             witness)
            (list
             '<
             (putnam-2002-b3-quoted threshold)
             (putnam-2002-b3-taylor-prefix-sum-term
              witness))))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2002-b3-quoted nil)
      (putnam-2002-b3-quoted t)))))

(defun putnam-2002-b3-less-than-e-p (threshold)
  (let ((failure-function
         (putnam-2002-b3-not-below-e-function threshold))
        (true-function
         (putnam-2002-b3-true-function)))
    (and
     (rationalp threshold)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

;; For positive k, the exponential-series tail after degree k is strictly
;; smaller than 1/(k*k!). Thus prefix_k + term_k/k is a rational upper bound
;; cofinal with exp(1). The function differs from constant true exactly when
;; one fully validated upper bound is below THRESHOLD, so NOT/FN-EQUAL
;; expresses exp(1) < THRESHOLD with an internal Taylor witness.
(defun putnam-2002-b3-not-above-e-function (threshold)
  (let* ((witness 'witness)
         (degree
          (list
           'binary-+
           (list 'len witness)
           (putnam-2002-b3-quoted -1)))
         (last-term
          (list 'nth degree witness))
         (upper-bound
          (list
           'binary-+
           (putnam-2002-b3-taylor-prefix-sum-term
            witness)
           (list
            'binary-*
            last-term
            (list 'unary-/ degree))))
         (qualification
          (putnam-2002-b3-and-terms
           (list
            (list 'true-listp witness)
            (list 'consp (list 'cdr witness))
            (putnam-2002-b3-taylor-prefix-valid-term
             witness)
            (list
             '<
             upper-bound
             (putnam-2002-b3-quoted threshold))))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2002-b3-quoted nil)
      (putnam-2002-b3-quoted t)))))

(defun putnam-2002-b3-e-less-than-p (threshold)
  (let ((failure-function
         (putnam-2002-b3-not-above-e-function threshold))
        (true-function
         (putnam-2002-b3-true-function)))
    (and
     (rationalp threshold)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnam-2002-b3-power-approximation (n)
  (expt (- 1 (/ 1 n)) n))

;; Since n>1, both exp(1) and (1-1/n)^n are positive. Multiplying the source
;; inequalities by exp(1) and dividing by the rational power shows that they
;; are respectively equivalent to
;;
;;   (1-1/n)/(1-1/n)^n < exp(1)
;;   exp(1) < (1-1/(2*n))/(1-1/n)^n.
;;
;; The two comparison predicates above are the exact strict order on this
;; computable real, not fixed-precision numerical approximations.
(defun putnambench-putnam-2002-b3-statement (n)
  (implies
   (and (integerp n)
        (< 1 n))
   (let ((power (putnam-2002-b3-power-approximation n)))
     (and
      (putnam-2002-b3-less-than-e-p
       (/ (- 1 (/ 1 n))
          power))
      (putnam-2002-b3-e-less-than-p
       (/ (- 1 (/ 1 (* 2 n)))
          power))))))

(value-triple :itpeval-statement-checked)
:q
