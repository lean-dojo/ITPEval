;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_a2:
;; arbitrarily large integers begin triples of consecutive integers, each a
;; sum of two integer squares. This file contains no proof.

(in-package "ACL2")

;; LOWER is the universally quantified integer lower bound.  The source's
;; existential integers m,a,b,c,d,e,f are kept internal as a seven-element
;; tuple.  FN-EQUAL compares the failure predicate with the constant-T
;; function on every ACL2 object, so its negation says exactly that some
;; integer tuple satisfies the strict bound and the three square-sum equations.

(defun putnam-2000-a2-quoted (object)
  (list 'quote object))

(defun putnam-2000-a2-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2000-a2-and-terms (cdr terms))
       (putnam-2000-a2-quoted nil))
    (putnam-2000-a2-quoted t)))

(defun putnam-2000-a2-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2000-a2-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2000-a2-square-term (value)
  (putnam-2000-a2-multiply-term value value))

(defun putnam-2000-a2-nth-term (index value)
  (list 'nth (putnam-2000-a2-quoted index) value))

(defun putnam-2000-a2-true-function ()
  '(lambda (witness) 't))

(defun putnam-2000-a2-witness-failure-function (lower)
  (let* ((m (putnam-2000-a2-nth-term 0 'witness))
         (a (putnam-2000-a2-nth-term 1 'witness))
         (b (putnam-2000-a2-nth-term 2 'witness))
         (c (putnam-2000-a2-nth-term 3 'witness))
         (d (putnam-2000-a2-nth-term 4 'witness))
         (e (putnam-2000-a2-nth-term 5 'witness))
         (f (putnam-2000-a2-nth-term 6 'witness))
         (qualification
          (putnam-2000-a2-and-terms
           (list
            (list 'true-listp 'witness)
            (list 'equal
                  (list 'len 'witness)
                  (putnam-2000-a2-quoted 7))
            (list 'integerp m)
            (list 'integerp a)
            (list 'integerp b)
            (list 'integerp c)
            (list 'integerp d)
            (list 'integerp e)
            (list 'integerp f)
            (list '< (putnam-2000-a2-quoted lower) m)
            (list
             'equal
             m
             (putnam-2000-a2-add-term
              (putnam-2000-a2-square-term a)
              (putnam-2000-a2-square-term b)))
            (list
             'equal
             (putnam-2000-a2-add-term
              m (putnam-2000-a2-quoted 1))
             (putnam-2000-a2-add-term
              (putnam-2000-a2-square-term c)
              (putnam-2000-a2-square-term d)))
            (list
             'equal
             (putnam-2000-a2-add-term
              m (putnam-2000-a2-quoted 2))
             (putnam-2000-a2-add-term
              (putnam-2000-a2-square-term e)
              (putnam-2000-a2-square-term f)))))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2000-a2-quoted nil)
      (putnam-2000-a2-quoted t)))))

(defun putnam-2000-a2-witness-exists-p (lower)
  (let ((failure-function
         (putnam-2000-a2-witness-failure-function lower))
        (true-function
         (putnam-2000-a2-true-function)))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2000-a2-statement (lower)
  (implies
   (integerp lower)
   (putnam-2000-a2-witness-exists-p lower)))

(value-triple :itpeval-statement-checked)
:q
