;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_a6:
;; an exact comparison between the numbers of 3-by-n column-permutation
;; matrices having consecutive row sums and having three equal row sums, for
;; some n at least 1995. This file contains no proof.

(in-package "ACL2")

;; A matrix is encoded by an integer from 0 through 6^n-1. Its n base-6
;; digits select, bijectively, the six permutations of (1,2,3). Subtracting 2
;; from each entry gives the digit contributions
;;
;;   0: (-1, 0, 1)    1: (-1, 1, 0)    2: (0,-1, 1)
;;   3: ( 0, 1,-1)    4: ( 1,-1, 0)    5: (1, 0,-1).
;;
;; The two summand functions below compute the first two centered row sums;
;; the third is their negative sum.

(defun putnam-1995-a6-quoted (object)
  (list 'quote object))

(defun putnam-1995-a6-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-1995-a6-and-terms (cdr terms))
       (putnam-1995-a6-quoted nil))
    (putnam-1995-a6-quoted t)))

(defun putnam-1995-a6-add-terms (terms)
  (if (consp terms)
      (list
       'binary-+
       (car terms)
       (putnam-1995-a6-add-terms (cdr terms)))
    (putnam-1995-a6-quoted 0)))

(defun putnam-1995-a6-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-1995-a6-list-term (cdr terms)))
    (putnam-1995-a6-quoted nil)))

(defun putnam-1995-a6-negate-term (value)
  (list 'unary-- value))

(defun putnam-1995-a6-subtract-term (left right)
  (list
   'binary-+
   left
   (putnam-1995-a6-negate-term right)))

(defun putnam-1995-a6-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1995-a6-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-1995-a6-quoted nil)
   (putnam-1995-a6-quoted t)))

(defun putnam-1995-a6-range-term (upper)
  (list
   'from-to-by
   (putnam-1995-a6-quoted 0)
   upper
   (putnam-1995-a6-quoted 1)))

(defun putnam-1995-a6-first-row-summand-function ()
  '(lambda (globals i)
     (if (equal
          (mod (floor (car globals) (expt '6 i)) '6)
          '0)
         '-1
       (if (equal
            (mod (floor (car globals) (expt '6 i)) '6)
            '1)
           '-1
         (if (equal
              (mod (floor (car globals) (expt '6 i)) '6)
              '2)
             '0
           (if (equal
                (mod (floor (car globals) (expt '6 i)) '6)
                '3)
               '0
             '1))))))

(defun putnam-1995-a6-second-row-summand-function ()
  '(lambda (globals i)
     (if (equal
          (mod (floor (car globals) (expt '6 i)) '6)
          '0)
         '0
       (if (equal
            (mod (floor (car globals) (expt '6 i)) '6)
            '1)
           '1
         (if (equal
              (mod (floor (car globals) (expt '6 i)) '6)
              '2)
             '-1
           (if (equal
                (mod (floor (car globals) (expt '6 i)) '6)
                '3)
               '1
             (if (equal
                  (mod (floor (car globals) (expt '6 i)) '6)
                  '4)
                 '-1
               '0)))))))

(defun putnam-1995-a6-row-sum-term
    (summand-function code n)
  (list
   'sum$+
   (putnam-1995-a6-quoted summand-function)
   (putnam-1995-a6-list-term (list code))
   (putnam-1995-a6-range-term
    (putnam-1995-a6-subtract-term
     n
     (putnam-1995-a6-quoted 1)))))

;; For fixed N, TARGET-X, and TARGET-Y, this function contributes one exactly
;; when CODE denotes a matrix with those first two centered row sums.
(defun putnam-1995-a6-target-indicator-function ()
  (let* ((n
          (list 'nth
                (putnam-1995-a6-quoted 0)
                'globals))
         (target-x
          (list 'nth
                (putnam-1995-a6-quoted 1)
                'globals))
         (target-y
          (list 'nth
                (putnam-1995-a6-quoted 2)
                'globals))
         (first-sum
          (putnam-1995-a6-row-sum-term
           (putnam-1995-a6-first-row-summand-function)
           'code
           n))
         (second-sum
          (putnam-1995-a6-row-sum-term
           (putnam-1995-a6-second-row-summand-function)
           'code
           n)))
    (list
     'lambda
     '(globals code)
     (list
      'if
      (putnam-1995-a6-and-terms
       (list
        (list 'equal first-sum target-x)
        (list 'equal second-sum target-y)))
      (putnam-1995-a6-quoted 1)
      (putnam-1995-a6-quoted 0)))))

(defun putnam-1995-a6-target-count-term (n target-x target-y)
  (list
   'sum$+
   (putnam-1995-a6-quoted
    (putnam-1995-a6-target-indicator-function))
   (putnam-1995-a6-list-term
    (list n target-x target-y))
   (putnam-1995-a6-range-term
    (putnam-1995-a6-subtract-term
     (list 'expt
           (putnam-1995-a6-quoted 6)
           n)
     (putnam-1995-a6-quoted 1)))))

;; Every matrix has total row sum 6*n. Hence three distinct consecutive row
;; sums must be 2*n-1, 2*n, 2*n+1, in one of six orders. After centering, the
;; six first-two-row targets are exactly the six pairs listed below. Equal row
;; sums have centered target (0,0). Thus these terms are precisely the two
;; finite cardinalities in the source statement.
(defun putnam-1995-a6-progression-count-term (n)
  (putnam-1995-a6-add-terms
   (list
    (putnam-1995-a6-target-count-term
     n
     (putnam-1995-a6-quoted -1)
     (putnam-1995-a6-quoted 0))
    (putnam-1995-a6-target-count-term
     n
     (putnam-1995-a6-quoted -1)
     (putnam-1995-a6-quoted 1))
    (putnam-1995-a6-target-count-term
     n
     (putnam-1995-a6-quoted 0)
     (putnam-1995-a6-quoted -1))
    (putnam-1995-a6-target-count-term
     n
     (putnam-1995-a6-quoted 0)
     (putnam-1995-a6-quoted 1))
    (putnam-1995-a6-target-count-term
     n
     (putnam-1995-a6-quoted 1)
     (putnam-1995-a6-quoted -1))
    (putnam-1995-a6-target-count-term
     n
     (putnam-1995-a6-quoted 1)
     (putnam-1995-a6-quoted 0)))))

(defun putnam-1995-a6-equal-count-term (n)
  (putnam-1995-a6-target-count-term
   n
   (putnam-1995-a6-quoted 0)
   (putnam-1995-a6-quoted 0)))

;; The failure function is false exactly at natural witnesses n >= 1995 for
;; which the progression count is at least four times the equal-sum count.
;; NOT/FN-EQUAL therefore retains the source's unbounded existential
;; quantifier without exposing n as a statement parameter or imposing a
;; finite search cutoff.
(defun putnam-1995-a6-witness-failure-function ()
  (let* ((progression-count
          (putnam-1995-a6-progression-count-term 'n))
         (equal-count
          (putnam-1995-a6-equal-count-term 'n))
         (qualification
          (putnam-1995-a6-and-terms
           (list
            (list 'natp 'n)
            (putnam-1995-a6-less-equal-term
             (putnam-1995-a6-quoted 1995)
             'n)
            (putnam-1995-a6-less-equal-term
             (putnam-1995-a6-multiply-term
              (putnam-1995-a6-quoted 4)
              equal-count)
             progression-count)))))
    (list
     'lambda
     '(n)
     (list
      'if
      qualification
      (putnam-1995-a6-quoted nil)
      (putnam-1995-a6-quoted t)))))

(defun putnam-1995-a6-true-function ()
  '(lambda (n) 't))

(defun putnambench-putnam-1995-a6-statement ()
  (let ((failure-function
         (putnam-1995-a6-witness-failure-function))
        (true-function
         (putnam-1995-a6-true-function)))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(value-triple :itpeval-statement-checked)
:q
