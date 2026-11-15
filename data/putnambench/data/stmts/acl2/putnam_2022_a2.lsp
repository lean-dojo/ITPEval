;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_a2:
;; among real polynomials of degree n, the largest possible number of negative
;; coefficients in the square is 2*n-2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The Lean statement, the Rocq statement, and the mathematical problem text
;; use degree n. The Isabelle source's degree 2*n is an isolated transcription
;; mismatch with those sources and with its own annotated answer.
;;
;; This statement uses rational coefficient lists as an exact, bidirectionally
;; equivalent presentation of the real-coefficient theorem, not as an
;; approximation. Every coefficient of P^2 is a polynomial expression in the
;; finitely many coefficients of P. Hence each strict sign condition and the
;; nonzero leading-coefficient condition persist on a neighborhood of P.
;; Density of Q in the real closed ordered field R therefore gives:
;;
;;   * a real counterexample to the rational upper bound can be approximated
;;     by a rational counterexample with the same required negative signs;
;;   * a real attaining polynomial can be approximated by a rational one
;;     retaining all its negative square coefficients and its degree;
;;   * every rational polynomial is itself a real polynomial.
;;
;; Thus the universal upper bound and existential attainment over rationals
;; together are logically equivalent to those same clauses over reals. This
;; concrete reduction is non-vacuous for every n: rational degree-n
;; coefficient lists exist (for example, the coefficient list of x^n).
;;
;; Polynomials are lists in ascending coefficient order. FN-EQUAL supplies the
;; internal universal polynomial quantifier, and negated FN-EQUAL supplies the
;; internal existential polynomial quantifier. The generated lambda bodies
;; contain only ACL2 primitives (IF, EQUAL, TRUE-LISTP, LEN, NTH, RATIONALP,
;; <, BINARY-+, and BINARY-*); no unwarranted user function occurs in either
;; FN-EQUAL operand.

(defun putnam-2022-a2-quoted (object)
  (list 'quote object))

(defun putnam-2022-a2-and-terms (terms)
  (if (endp terms)
      (putnam-2022-a2-quoted t)
    (list
     'if
     (car terms)
     (putnam-2022-a2-and-terms (cdr terms))
     (putnam-2022-a2-quoted nil))))

(defun putnam-2022-a2-not-term (term)
  (list
   'if
   term
   (putnam-2022-a2-quoted nil)
   (putnam-2022-a2-quoted t)))

(defun putnam-2022-a2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2022-a2-quoted t)))

(defun putnam-2022-a2-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-2022-a2-quoted nil)
   (putnam-2022-a2-quoted t)))

(defun putnam-2022-a2-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2022-a2-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2022-a2-sum-terms (terms)
  (if (endp terms)
      (putnam-2022-a2-quoted 0)
    (putnam-2022-a2-add-term
     (car terms)
     (putnam-2022-a2-sum-terms (cdr terms)))))

(defun putnam-2022-a2-nth-term (index polynomial)
  (list
   'nth
   (putnam-2022-a2-quoted (nfix index))
   polynomial))

(defun putnam-2022-a2-rational-coefficient-terms
    (remaining polynomial)
  (if (zp remaining)
      nil
    (cons
     (list
      'rationalp
      (putnam-2022-a2-nth-term
       (1- remaining) polynomial))
     (putnam-2022-a2-rational-coefficient-terms
      (1- remaining) polynomial))))

(defun putnam-2022-a2-degree-n-polynomial-term
    (polynomial n)
  (let ((degree (nfix n)))
    (putnam-2022-a2-and-terms
     (append
      (list
       (list 'true-listp polynomial)
       (list
        'equal
        (list 'len polynomial)
        (putnam-2022-a2-quoted (+ degree 1))))
      (putnam-2022-a2-rational-coefficient-terms
       (+ degree 1) polynomial)
      (list
       (putnam-2022-a2-not-term
        (list
         'equal
         (putnam-2022-a2-nth-term degree polynomial)
         (putnam-2022-a2-quoted 0))))))))

(defun putnam-2022-a2-square-coefficient-products
    (remaining index degree coefficient polynomial)
  (if (zp remaining)
      nil
    (let* ((i (nfix index))
           (n (nfix degree))
           (k (nfix coefficient))
           (j (- k i))
           (rest
            (putnam-2022-a2-square-coefficient-products
             (1- remaining) (+ i 1) n k polynomial)))
      (if (and (<= i k) (<= j n))
          (cons
           (putnam-2022-a2-multiply-term
            (putnam-2022-a2-nth-term i polynomial)
            (putnam-2022-a2-nth-term j polynomial))
           rest)
        rest))))

(defun putnam-2022-a2-square-coefficient-term
    (degree coefficient polynomial)
  (let ((n (nfix degree))
        (k (nfix coefficient)))
    (putnam-2022-a2-sum-terms
     (putnam-2022-a2-square-coefficient-products
      (+ n 1) 0 n k polynomial))))

(defun putnam-2022-a2-negative-indicator-terms
    (remaining coefficient degree polynomial)
  (if (zp remaining)
      nil
    (let ((k (nfix coefficient))
          (n (nfix degree)))
      (cons
       (list
        'if
        (list
         '<
         (putnam-2022-a2-square-coefficient-term
          n k polynomial)
         (putnam-2022-a2-quoted 0))
        (putnam-2022-a2-quoted 1)
        (putnam-2022-a2-quoted 0))
       (putnam-2022-a2-negative-indicator-terms
        (1- remaining) (+ k 1) n polynomial)))))

(defun putnam-2022-a2-negative-square-count-term
    (polynomial n)
  (let ((degree (nfix n)))
    (putnam-2022-a2-sum-terms
     (putnam-2022-a2-negative-indicator-terms
      (+ (* 2 degree) 1) 0 degree polynomial))))

(defun putnam-2022-a2-solution (n)
  (- (* 2 (nfix n)) 2))

(defun putnam-2022-a2-true-function ()
  '(lambda (polynomial) 't))

(defun putnam-2022-a2-upper-bound-function (n)
  (let* ((polynomial 'polynomial)
         (degree (nfix n))
         (domain
          (putnam-2022-a2-degree-n-polynomial-term
           polynomial degree))
         (count
          (putnam-2022-a2-negative-square-count-term
           polynomial degree)))
    (list
     'lambda
     '(polynomial)
     (putnam-2022-a2-implies-term
      domain
      (putnam-2022-a2-less-equal-term
       count
       (putnam-2022-a2-quoted
        (putnam-2022-a2-solution degree)))))))

(defun putnam-2022-a2-attainment-failure-function (n)
  (let* ((polynomial 'polynomial)
         (degree (nfix n))
         (domain
          (putnam-2022-a2-degree-n-polynomial-term
           polynomial degree))
         (count
          (putnam-2022-a2-negative-square-count-term
           polynomial degree)))
    (list
     'lambda
     '(polynomial)
     (list
      'if
      (putnam-2022-a2-and-terms
       (list
        domain
        (list
         'equal
         count
         (putnam-2022-a2-quoted
          (putnam-2022-a2-solution degree)))))
      (putnam-2022-a2-quoted nil)
      (putnam-2022-a2-quoted t)))))

(defun putnam-2022-a2-quantifier-functions-tame-p (n)
  (and
   (tamep-functionp
    (putnam-2022-a2-upper-bound-function n))
   (tamep-functionp
    (putnam-2022-a2-attainment-failure-function n))
   (tamep-functionp
    (putnam-2022-a2-true-function))))

(defun putnam-2022-a2-upper-bound-p (n)
  (let ((condition
         (putnam-2022-a2-upper-bound-function n))
        (always-true
         (putnam-2022-a2-true-function)))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnam-2022-a2-attainment-p (n)
  (let ((failure
         (putnam-2022-a2-attainment-failure-function n))
        (always-true
         (putnam-2022-a2-true-function)))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnambench-putnam-2022-a2-statement (n)
  (implies
   (and
    (natp n)
    (<= 2 n))
   (and
    (putnam-2022-a2-quantifier-functions-tame-p n)
    (putnam-2022-a2-upper-bound-p n)
    (putnam-2022-a2-attainment-p n))))

(value-triple :itpeval-statement-checked)
:q
