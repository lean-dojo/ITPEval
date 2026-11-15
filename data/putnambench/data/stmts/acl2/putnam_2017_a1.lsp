;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_a1:
;; the positive integers outside the least set containing 2 and closed under
;; positive square roots and the map n |-> (n+5)^2 are exactly 1 and the
;; positive multiples of 5. This file contains no proof.

(in-package "ACL2")

;; A finite trace lists derivation records (value rule parent-index). Each
;; value is either 2, (m+5)^2 for an earlier value m, or a positive square root
;; of an earlier value. The integers admitting such traces form exactly the
;; least qualifying set: appending one record proves closure under both source
;; rules, while induction along a trace puts every trace value in every
;; qualifying set.
;;
;; Negated FN-EQUAL keeps the finite trace existentially quantified inside the
;; statement predicate. It does not replace the resulting potentially infinite
;; least set by a finite carrier or expose the trace as an external parameter.

(defun putnam-2017-a1-quoted (object)
  (list 'quote object))

(defun putnam-2017-a1-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2017-a1-list-term (cdr terms)))
    (putnam-2017-a1-quoted nil)))

(defun putnam-2017-a1-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2017-a1-and-terms (cdr terms))
       (putnam-2017-a1-quoted nil))
    (putnam-2017-a1-quoted t)))

(defun putnam-2017-a1-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2017-a1-quoted t)
       (putnam-2017-a1-or-terms (cdr terms)))
    (putnam-2017-a1-quoted nil)))

(defun putnam-2017-a1-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2017-a1-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2017-a1-nth-term (index values)
  (list 'nth index values))

(defun putnam-2017-a1-range-term (upper)
  (list
   'from-to-by
   (putnam-2017-a1-quoted 0)
   upper
   (putnam-2017-a1-quoted 1)))

(defun putnam-2017-a1-iteration-term (values)
  (list
   'loop$-as
   (putnam-2017-a1-list-term (list values))))

(defun putnam-2017-a1-true-function ()
  (list 'lambda '(trace) (putnam-2017-a1-quoted t)))

(defun putnam-2017-a1-entry-function ()
  (let* ((index (list 'car 'row))
         (trace (list 'car 'globals))
         (entry
          (putnam-2017-a1-nth-term index trace))
         (value
          (putnam-2017-a1-nth-term
           (putnam-2017-a1-quoted 0)
           entry))
         (rule
          (putnam-2017-a1-nth-term
           (putnam-2017-a1-quoted 1)
           entry))
         (parent-index
          (putnam-2017-a1-nth-term
           (putnam-2017-a1-quoted 2)
           entry))
         (parent-entry
          (putnam-2017-a1-nth-term parent-index trace))
         (parent-value
          (putnam-2017-a1-nth-term
           (putnam-2017-a1-quoted 0)
           parent-entry))
         (parent-before-p
          (putnam-2017-a1-and-terms
           (list
            (list 'natp parent-index)
            (list '< parent-index index))))
         (parent-plus-five
          (putnam-2017-a1-add-term
           parent-value
           (putnam-2017-a1-quoted 5)))
         (base-step
          (putnam-2017-a1-and-terms
           (list
            (list
             'equal rule
             (putnam-2017-a1-quoted 0))
            (list
             'equal value
             (putnam-2017-a1-quoted 2)))))
         (forward-step
          (putnam-2017-a1-and-terms
           (list
            (list
             'equal rule
             (putnam-2017-a1-quoted 1))
            parent-before-p
            (list
             'equal
             value
             (putnam-2017-a1-multiply-term
              parent-plus-five parent-plus-five)))))
         (square-root-step
          (putnam-2017-a1-and-terms
           (list
            (list
             'equal rule
             (putnam-2017-a1-quoted 2))
            parent-before-p
            (list
             'equal
             parent-value
             (putnam-2017-a1-multiply-term
              value value))))))
    (list
     'lambda
     '(globals row)
     (putnam-2017-a1-and-terms
      (list
       (list 'true-listp entry)
       (list
        'equal
        (list 'len entry)
        (putnam-2017-a1-quoted 3))
       (list 'integerp value)
       (list '< (putnam-2017-a1-quoted 0) value)
       (putnam-2017-a1-or-terms
        (list base-step forward-step square-root-step)))))))

(defun putnam-2017-a1-all-indices-term
    (entry-function globals upper)
  (list
   'always$+
   (putnam-2017-a1-quoted entry-function)
   globals
   (putnam-2017-a1-iteration-term
    (putnam-2017-a1-range-term upper))))

(defun putnam-2017-a1-trace-failure-function
    (target entry-function)
  (let* ((trace 'trace)
         (upper
          (putnam-2017-a1-add-term
           (list 'len trace)
           (putnam-2017-a1-quoted -1)))
         (globals
          (putnam-2017-a1-list-term (list trace)))
         (last-entry
          (putnam-2017-a1-nth-term upper trace))
         (last-value
          (putnam-2017-a1-nth-term
           (putnam-2017-a1-quoted 0)
           last-entry))
         (qualification
          (putnam-2017-a1-and-terms
           (list
            (list 'true-listp trace)
            (list 'consp trace)
            (putnam-2017-a1-all-indices-term
             entry-function globals upper)
            (list
             'equal
             last-value
             (putnam-2017-a1-quoted target))))))
    (list
     'lambda
     '(trace)
     (list
      'if
      qualification
      (putnam-2017-a1-quoted nil)
      (putnam-2017-a1-quoted t)))))

(defun putnam-2017-a1-in-least-set-p (n)
  (let* ((entry-function
          (putnam-2017-a1-entry-function))
         (failure-function
          (putnam-2017-a1-trace-failure-function
           n entry-function))
        (true-function
         (putnam-2017-a1-true-function)))
    (and
     (tamep-functionp entry-function)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

(defun putnam-2017-a1-solution-member-p (n)
  (and
   (integerp n)
   (< 0 n)
   (or (equal n 1)
       (equal (mod n 5) 0))))

;; ACL2 universally closes N. Restricting it to integers preserves the source
;; domain, and this IFF is the pointwise form of the source set equality.
(defun putnambench-putnam-2017-a1-statement (n)
  (implies
   (integerp n)
   (iff
    (and
     (< 0 n)
     (not (putnam-2017-a1-in-least-set-p n)))
    (putnam-2017-a1-solution-member-p n))))

(value-triple :itpeval-statement-checked)
:q
