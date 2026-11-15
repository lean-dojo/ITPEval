;; Statement-only formalization of PutnamBench corpus artifact putnam_1962_b2:
;; existence of a function from the real line to subsets of the natural
;; numbers that sends strict order to proper inclusion. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Real numbers are rounded, nontrivial lower Dedekind cuts of the rationals.
;; Natural-number sets and the requested function are tame APPLY$ objects.
;; FN-EQUAL supplies unbounded universal quantification, while inequality with
;; a constant-false function keeps every existential witness internal.
;;
;; Boolean-valued cuts are canonical: equality is extensional equality, and
;; strict real order is proper inclusion of lower cuts. The output function is
;; required to be extensional on equal cuts. Replacing positive naturals by
;; naturals is equivalent through a fixed bijection. Conversely, the standard
;; rational enumeration sends each cut to the natural codes of the rationals
;; it contains, so the tame-function presentation does not restrict the
;; source existence assertion.

(defun putnam-1962-b2-quoted (object)
  (list 'quote object))

(defun putnam-1962-b2-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-1962-b2-term-list (cdr terms)))
    (putnam-1962-b2-quoted nil)))

(defun putnam-1962-b2-apply-term
    (function-term arguments)
  (list
   'apply$
   function-term
   (putnam-1962-b2-term-list arguments)))

(defun putnam-1962-b2-static-apply-term
    (function arguments)
  (putnam-1962-b2-apply-term
   (putnam-1962-b2-quoted function)
   arguments))

(defun putnam-1962-b2-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-1962-b2-and-terms (cdr terms))
       (putnam-1962-b2-quoted nil))
    (putnam-1962-b2-quoted t)))

(defun putnam-1962-b2-not-term (term)
  (list
   'if
   term
   (putnam-1962-b2-quoted nil)
   (putnam-1962-b2-quoted t)))

(defun putnam-1962-b2-implies-term
    (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (putnam-1962-b2-quoted t)))

(defun putnam-1962-b2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-1962-b2-quoted t)))

(defun putnam-1962-b2-false-function (formals)
  (list
   'lambda
   formals
   (putnam-1962-b2-quoted nil)))

(defun putnam-1962-b2-universal-p
    (function formals)
  (let ((always-true
         (putnam-1962-b2-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun putnam-1962-b2-exists-p
    (function formals)
  (let ((always-false
         (putnam-1962-b2-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun putnam-1962-b2-member-p
    (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

;; Dedekind-cut presentation of the full real line.

(defun putnam-1962-b2-boolean-value-at-p
    (predicate object)
  (let ((value (apply$ predicate (list object))))
    (or (equal value t)
        (equal value nil))))

(defun putnam-1962-b2-boolean-function
    (predicate)
  (list
   'lambda
   '(object)
   (list
    'putnam-1962-b2-boolean-value-at-p
    (putnam-1962-b2-quoted predicate)
    'object)))

(defun putnam-1962-b2-lower-law-at-p
    (cut q r)
  (implies
   (and
    (rationalp q)
    (rationalp r)
    (< q r)
    (putnam-1962-b2-member-p cut r))
   (putnam-1962-b2-member-p cut q)))

(defun putnam-1962-b2-lower-law-function
    (cut)
  (list
   'lambda
   '(q r)
   (list
    'putnam-1962-b2-lower-law-at-p
    (putnam-1962-b2-quoted cut)
    'q
    'r)))

(defun putnam-1962-b2-rounded-witness-at-p
    (cut q r)
  (and
   (rationalp r)
   (< q r)
   (putnam-1962-b2-member-p cut r)))

(defun putnam-1962-b2-rounded-witness-function
    (cut q)
  (list
   'lambda
   '(r)
   (list
    'putnam-1962-b2-rounded-witness-at-p
    (putnam-1962-b2-quoted cut)
    (putnam-1962-b2-quoted q)
    'r)))

(defun putnam-1962-b2-rounded-law-at-p
    (cut q)
  (implies
   (and
    (rationalp q)
    (putnam-1962-b2-member-p cut q))
   (putnam-1962-b2-exists-p
    (putnam-1962-b2-rounded-witness-function cut q)
    '(r))))

(defun putnam-1962-b2-rounded-law-function
    (cut)
  (list
   'lambda
   '(q)
   (list
    'putnam-1962-b2-rounded-law-at-p
    (putnam-1962-b2-quoted cut)
    'q)))

(defun putnam-1962-b2-rational-support-at-p
    (cut object)
  (implies
   (not (rationalp object))
   (not (putnam-1962-b2-member-p cut object))))

(defun putnam-1962-b2-rational-support-function
    (cut)
  (list
   'lambda
   '(object)
   (list
    'putnam-1962-b2-rational-support-at-p
    (putnam-1962-b2-quoted cut)
    'object)))

(defun putnam-1962-b2-lower-witness-at-p
    (cut q)
  (and
   (rationalp q)
   (putnam-1962-b2-member-p cut q)))

(defun putnam-1962-b2-lower-witness-function
    (cut)
  (list
   'lambda
   '(q)
   (list
    'putnam-1962-b2-lower-witness-at-p
    (putnam-1962-b2-quoted cut)
    'q)))

(defun putnam-1962-b2-upper-witness-at-p
    (cut q)
  (and
   (rationalp q)
   (not (putnam-1962-b2-member-p cut q))))

(defun putnam-1962-b2-upper-witness-function
    (cut)
  (list
   'lambda
   '(q)
   (list
    'putnam-1962-b2-upper-witness-at-p
    (putnam-1962-b2-quoted cut)
    'q)))

(defun putnam-1962-b2-real-p (cut)
  (and
   (tamep-functionp cut)
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-boolean-function cut)
    '(object))
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-lower-law-function cut)
    '(q r))
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-rounded-law-function cut)
    '(q))
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-rational-support-function cut)
    '(object))
   (putnam-1962-b2-exists-p
    (putnam-1962-b2-lower-witness-function cut)
    '(q))
   (putnam-1962-b2-exists-p
    (putnam-1962-b2-upper-witness-function cut)
    '(q))))

(defun putnam-1962-b2-cut-subset-at-p
    (left right q)
  (implies
   (and
    (rationalp q)
    (putnam-1962-b2-member-p left q))
   (putnam-1962-b2-member-p right q)))

(defun putnam-1962-b2-cut-subset-function
    (left right)
  (list
   'lambda
   '(q)
   (list
    'putnam-1962-b2-cut-subset-at-p
    (putnam-1962-b2-quoted left)
    (putnam-1962-b2-quoted right)
    'q)))

(defun putnam-1962-b2-cut-subset-p
    (left right)
  (putnam-1962-b2-universal-p
   (putnam-1962-b2-cut-subset-function left right)
   '(q)))

(defun putnam-1962-b2-cut-difference-at-p
    (left right q)
  (and
   (rationalp q)
   (putnam-1962-b2-member-p right q)
   (not (putnam-1962-b2-member-p left q))))

(defun putnam-1962-b2-cut-difference-function
    (left right)
  (list
   'lambda
   '(q)
   (list
    'putnam-1962-b2-cut-difference-at-p
    (putnam-1962-b2-quoted left)
    (putnam-1962-b2-quoted right)
    'q)))

(defun putnam-1962-b2-real-equal-p
    (left right)
  (and
   (putnam-1962-b2-real-p left)
   (putnam-1962-b2-real-p right)
   (fn-equal left right)))

(defun putnam-1962-b2-real-less-p
    (left right)
  (and
   (putnam-1962-b2-real-p left)
   (putnam-1962-b2-real-p right)
   (putnam-1962-b2-cut-subset-p left right)
   (putnam-1962-b2-exists-p
    (putnam-1962-b2-cut-difference-function left right)
    '(q))))

;; Subsets of the natural numbers.

(defun putnam-1962-b2-natural-support-at-p
    (set object)
  (implies
   (not (natp object))
   (not (putnam-1962-b2-member-p set object))))

(defun putnam-1962-b2-natural-support-function
    (set)
  (list
   'lambda
   '(object)
   (list
    'putnam-1962-b2-natural-support-at-p
    (putnam-1962-b2-quoted set)
    'object)))

(defun putnam-1962-b2-natural-set-p (set)
  (and
   (tamep-functionp set)
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-boolean-function set)
    '(object))
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-natural-support-function set)
    '(object))))

(defun putnam-1962-b2-natural-subset-at-p
    (left right n)
  (implies
   (and
    (natp n)
    (putnam-1962-b2-member-p left n))
   (putnam-1962-b2-member-p right n)))

(defun putnam-1962-b2-natural-subset-function
    (left right)
  (list
   'lambda
   '(n)
   (list
    'putnam-1962-b2-natural-subset-at-p
    (putnam-1962-b2-quoted left)
    (putnam-1962-b2-quoted right)
    'n)))

(defun putnam-1962-b2-natural-difference-at-p
    (left right n)
  (and
   (natp n)
   (putnam-1962-b2-member-p right n)
   (not (putnam-1962-b2-member-p left n))))

(defun putnam-1962-b2-natural-difference-function
    (left right)
  (list
   'lambda
   '(n)
   (list
    'putnam-1962-b2-natural-difference-at-p
    (putnam-1962-b2-quoted left)
    (putnam-1962-b2-quoted right)
    'n)))

(defun putnam-1962-b2-natural-set-equal-p
    (left right)
  (and
   (putnam-1962-b2-natural-set-p left)
   (putnam-1962-b2-natural-set-p right)
   (fn-equal left right)))

(defun putnam-1962-b2-proper-natural-subset-p
    (left right)
  (and
   (putnam-1962-b2-natural-set-p left)
   (putnam-1962-b2-natural-set-p right)
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-natural-subset-function
     left right)
    '(n))
   (putnam-1962-b2-exists-p
    (putnam-1962-b2-natural-difference-function
     left right)
    '(n))))

;; The source quantifier order is preserved:
;; exists f, for every real a and b, a < b implies f(a) is a proper subset
;; of f(b).

(defun putnam-1962-b2-function-output-function
    (function)
  (let ((output
         (putnam-1962-b2-static-apply-term
          function
          '(x))))
    (list
     'lambda
     '(x)
     (putnam-1962-b2-implies-term
      (list 'putnam-1962-b2-real-p 'x)
      (list
       'putnam-1962-b2-natural-set-p
       output)))))

(defun putnam-1962-b2-function-extensional-function
    (function)
  (let ((left-output
         (putnam-1962-b2-static-apply-term
          function
          '(left)))
        (right-output
         (putnam-1962-b2-static-apply-term
          function
          '(right))))
    (list
     'lambda
     '(left right)
     (putnam-1962-b2-implies-term
      (putnam-1962-b2-and-terms
       (list
        (list 'putnam-1962-b2-real-p 'left)
        (list 'putnam-1962-b2-real-p 'right)
        (list
         'putnam-1962-b2-real-equal-p
         'left
         'right)))
      (list
       'putnam-1962-b2-natural-set-equal-p
       left-output
       right-output)))))

(defun putnam-1962-b2-strict-inclusion-function
    (function)
  (let ((left-output
         (putnam-1962-b2-static-apply-term
          function
          '(left)))
        (right-output
         (putnam-1962-b2-static-apply-term
          function
          '(right))))
    (list
     'lambda
     '(left right)
     (putnam-1962-b2-implies-term
      (putnam-1962-b2-and-terms
       (list
        (list 'putnam-1962-b2-real-p 'left)
        (list 'putnam-1962-b2-real-p 'right)
        (list
         'putnam-1962-b2-real-less-p
         'left
         'right)))
      (list
       'putnam-1962-b2-proper-natural-subset-p
       left-output
       right-output)))))

(defun putnam-1962-b2-function-witness-p
    (function)
  (and
   (tamep-functionp function)
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-function-output-function function)
    '(x))
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-function-extensional-function
     function)
    '(left right))
   (putnam-1962-b2-universal-p
    (putnam-1962-b2-strict-inclusion-function
     function)
    '(left right))))

(defun putnam-1962-b2-function-witness-function ()
  (list
   'lambda
   '(function)
   (list
    'putnam-1962-b2-function-witness-p
    'function)))

(defun putnambench-putnam-1962-b2-statement ()
  (putnam-1962-b2-exists-p
   (putnam-1962-b2-function-witness-function)
   '(function)))

(value-triple :itpeval-statement-checked)
:q
