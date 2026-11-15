;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_a2:
;; binary operations satisfying both involution laws are commutative, but
;; need not be associative. This file contains no proof.

(in-package "ACL2")

;; CARRIER and OP are ACL2 function objects. The generated predicate lambdas
;; return T outside CARRIER, so FN-EQUAL with the matching constant-T lambda
;; expresses universal quantification over exactly the represented type.

(defun putnam-1972-a2-quoted (object)
  (list 'quote object))

(defun putnam-1972-a2-apply1-term (function argument)
  (list 'apply$
        (putnam-1972-a2-quoted function)
        (list 'cons argument nil)))

(defun putnam-1972-a2-apply2-term (function left right)
  (list 'apply$
        (putnam-1972-a2-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1972-a2-carrier-term (carrier element)
  (putnam-1972-a2-apply1-term carrier element))

(defun putnam-1972-a2-operation-term (op left right)
  (putnam-1972-a2-apply2-term op left right))

(defun putnam-1972-a2-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      t
    (list 'if
          (putnam-1972-a2-carrier-term
           carrier (car variables))
          (putnam-1972-a2-all-in-carrier-term
           carrier (cdr variables))
          nil)))

(defun putnam-1972-a2-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1972-a2-all-in-carrier-term
         carrier variables)
        proposition
        t))

(defun putnam-1972-a2-true-function (formals)
  (list 'lambda formals t))

(defun putnam-1972-a2-closure-function (carrier op)
  (let ((op-xy
         (putnam-1972-a2-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1972-a2-restricted-predicate-term
      carrier
      '(x y)
      (putnam-1972-a2-carrier-term carrier op-xy)))))

(defun putnam-1972-a2-left-involution-function (carrier op)
  (let ((op-xy
         (putnam-1972-a2-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1972-a2-restricted-predicate-term
      carrier
      '(x y)
      (list
       'equal
       (putnam-1972-a2-operation-term op 'x op-xy)
       'y)))))

(defun putnam-1972-a2-right-involution-function (carrier op)
  (let ((op-yx
         (putnam-1972-a2-operation-term op 'y 'x)))
    (list
     'lambda
     '(x y)
     (putnam-1972-a2-restricted-predicate-term
      carrier
      '(x y)
      (list
       'equal
       (putnam-1972-a2-operation-term op op-yx 'x)
       'y)))))

(defun putnam-1972-a2-commutative-function (carrier op)
  (list
   'lambda
   '(x y)
   (putnam-1972-a2-restricted-predicate-term
    carrier
    '(x y)
    (list
     'equal
     (putnam-1972-a2-operation-term op 'x 'y)
     (putnam-1972-a2-operation-term op 'y 'x)))))

(defun putnam-1972-a2-involution-structure-p (carrier op)
  (and
   (tamep-functionp carrier)
   (tamep-functionp op)
   (fn-equal
    (putnam-1972-a2-closure-function carrier op)
    (putnam-1972-a2-true-function '(x y)))
   (fn-equal
    (putnam-1972-a2-left-involution-function carrier op)
    (putnam-1972-a2-true-function '(x y)))
   (fn-equal
    (putnam-1972-a2-right-involution-function carrier op)
    (putnam-1972-a2-true-function '(x y)))))

(defun putnam-1972-a2-universal-part-p (carrier op)
  (implies
   (putnam-1972-a2-involution-structure-p carrier op)
   (fn-equal
    (putnam-1972-a2-commutative-function carrier op)
    (putnam-1972-a2-true-function '(x y)))))

;; The source asks only for existence of a nonassociative example. Keep the
;; carrier, operation, and nonassociativity witness under internal quantifiers.
(defun-sk putnam-1972-a2-nonassociative-p (carrier op)
  (exists (x y z)
    (and
     (apply$ carrier (list x))
     (apply$ carrier (list y))
     (apply$ carrier (list z))
     (not
      (equal
       (apply$ op
               (list x (apply$ op (list y z))))
       (apply$ op
               (list (apply$ op (list x y)) z)))))))

(defun putnam-1972-a2-nonassociative-structure-p (carrier op)
  (and
   (putnam-1972-a2-involution-structure-p carrier op)
   (putnam-1972-a2-nonassociative-p carrier op)))

(defun-sk putnam-1972-a2-nonassociative-example-exists-p ()
  (exists (carrier op)
    (putnam-1972-a2-nonassociative-structure-p carrier op)))

(defun putnambench-putnam-1972-a2-statement (carrier op)
  (and
   (putnam-1972-a2-universal-part-p carrier op)
   (putnam-1972-a2-nonassociative-example-exists-p)))

(value-triple :itpeval-statement-checked)
:q
