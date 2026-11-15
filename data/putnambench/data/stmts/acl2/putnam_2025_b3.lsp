;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_b3:
;; every positive integer is reachable from every other by repeatedly taking
;; positive divisors of 2025^n - 15^n. This file contains no proof.

(in-package "ACL2")

(defun putnam-2025-b3-quoted (object)
  (list 'quote object))

(defun putnam-2025-b3-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2025-b3-list-term (cdr terms)))
    (putnam-2025-b3-quoted nil)))

(defun putnam-2025-b3-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2025-b3-and-terms (cdr terms))
       (putnam-2025-b3-quoted nil))
    (putnam-2025-b3-quoted t)))

(defun putnam-2025-b3-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2025-b3-subtract-term (left right)
  (putnam-2025-b3-add-term
   left
   (list 'unary-- right)))

(defun putnam-2025-b3-expt-term (base exponent)
  (list 'expt base exponent))

(defun putnam-2025-b3-nth-term (index sequence)
  (list 'nth index sequence))

(defun putnam-2025-b3-singleton-function ()
  '(lambda (index)
     (cons index 'nil)))

(defun putnam-2025-b3-wrapped-range-term (lower upper)
  (list
   'collect$
   (putnam-2025-b3-quoted
    (putnam-2025-b3-singleton-function))
   (list
    'from-to-by
    lower
    upper
    (putnam-2025-b3-quoted 1))))

;; A path step from n to d requires positive integers n and d and the exact
;; source divisibility condition d | (2025^n - 15^n).
(defun putnam-2025-b3-path-step-function ()
  (let* ((path (list 'car 'loop$-gvars))
         (index (list 'car 'loop$-ivars))
         (next-index
          (putnam-2025-b3-add-term
           index
           (putnam-2025-b3-quoted 1)))
         (current
          (putnam-2025-b3-nth-term index path))
         (next
          (putnam-2025-b3-nth-term next-index path))
         (difference
          (putnam-2025-b3-subtract-term
           (putnam-2025-b3-expt-term
            (putnam-2025-b3-quoted 2025)
            current)
           (putnam-2025-b3-expt-term
            (putnam-2025-b3-quoted 15)
            current)))
         (body
          (putnam-2025-b3-and-terms
           (list
            (list 'integerp current)
            (list '< (putnam-2025-b3-quoted 0) current)
            (list 'integerp next)
            (list '< (putnam-2025-b3-quoted 0) next)
            (list
             'equal
             (list 'mod difference next)
             (putnam-2025-b3-quoted 0))))))
    (list
     'lambda
     '(loop$-gvars loop$-ivars)
     body)))

(defun putnam-2025-b3-path-valid-term (path)
  (let ((short-path
         (list
          '<
          (list 'len path)
          (putnam-2025-b3-quoted 2))))
    (list
     'if
     short-path
     (putnam-2025-b3-quoted t)
     (list
      'always$+
      (putnam-2025-b3-quoted
       (putnam-2025-b3-path-step-function))
      (putnam-2025-b3-list-term (list path))
      (putnam-2025-b3-wrapped-range-term
       (putnam-2025-b3-quoted 0)
       (putnam-2025-b3-add-term
        (list 'len path)
        (putnam-2025-b3-quoted -2)))))))

;; For a directed graph, every nonempty forward-closed subset is the whole
;; vertex set iff every target is reachable from every start by a finite path.
;; Thus this finite-path formulation is bidirectionally equivalent to the
;; source's quantification over arbitrary sets of positive integers.
(defun putnam-2025-b3-witness-failure-function (start target)
  (let* ((path 'path)
         (last-index
          (putnam-2025-b3-add-term
           (list 'len path)
           (putnam-2025-b3-quoted -1)))
         (qualification
          (putnam-2025-b3-and-terms
           (list
            (list 'true-listp path)
            (list 'consp path)
            (list
             'equal
             (list 'car path)
             (putnam-2025-b3-quoted start))
            (list
             'equal
             (putnam-2025-b3-nth-term last-index path)
             (putnam-2025-b3-quoted target))
            (putnam-2025-b3-path-valid-term path)))))
    (list
     'lambda
     '(path)
     (list
      'if
      qualification
      (putnam-2025-b3-quoted nil)
      (putnam-2025-b3-quoted t)))))

(defun putnam-2025-b3-true-function ()
  (list
   'lambda
   '(path)
   (putnam-2025-b3-quoted t)))

;; Inequality with the constant-true predicate expresses the internal
;; existential quantifier over arbitrary finite paths.
(defun putnambench-putnam-2025-b3-statement (start target)
  (implies
   (and
    (integerp start)
    (< 0 start)
    (integerp target)
    (< 0 target))
   (let ((failure
          (putnam-2025-b3-witness-failure-function
           start target))
         (always-true
          (putnam-2025-b3-true-function)))
     (and
      (tamep-functionp failure)
      (tamep-functionp always-true)
      (not (fn-equal failure always-true))))))

(value-triple :itpeval-statement-checked)
:q
