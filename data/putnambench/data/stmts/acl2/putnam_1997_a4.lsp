;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_a4:
;; a function on an arbitrary group whose triple product is constant on
;; triples multiplying to the identity can be left-translated into a group
;; homomorphism. This file contains no proof.

(in-package "ACL2")

;; CARRIER, OP, INV, and PHI are ACL2 function objects. Generated predicate
;; lambdas return T outside CARRIER, so FN-EQUAL against a constant-T lambda
;; expresses universal quantification over exactly the represented group.

(defun putnam-1997-a4-quoted (object)
  (list 'quote object))

(defun putnam-1997-a4-apply1-term (function argument)
  (list 'apply$
        (putnam-1997-a4-quoted function)
        (list 'cons argument nil)))

(defun putnam-1997-a4-apply2-term (function left right)
  (list 'apply$
        (putnam-1997-a4-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1997-a4-carrier-term (carrier element)
  (putnam-1997-a4-apply1-term carrier element))

(defun putnam-1997-a4-operation-term (op left right)
  (putnam-1997-a4-apply2-term op left right))

(defun putnam-1997-a4-inverse-term (inv element)
  (putnam-1997-a4-apply1-term inv element))

(defun putnam-1997-a4-phi-term (phi element)
  (putnam-1997-a4-apply1-term phi element))

(defun putnam-1997-a4-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-1997-a4-quoted t)
    (list 'if
          (putnam-1997-a4-carrier-term
           carrier (car variables))
          (putnam-1997-a4-all-in-carrier-term
           carrier (cdr variables))
          (putnam-1997-a4-quoted nil))))

(defun putnam-1997-a4-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1997-a4-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-1997-a4-quoted t)))

(defun putnam-1997-a4-and-term (left right)
  (list 'if left right (putnam-1997-a4-quoted nil)))

(defun putnam-1997-a4-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (putnam-1997-a4-quoted t)))

(defun putnam-1997-a4-true-function (formals)
  (list 'lambda formals (putnam-1997-a4-quoted t)))

(defun putnam-1997-a4-operation-closure-function (carrier op)
  (let ((op-xy
         (putnam-1997-a4-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1997-a4-restricted-predicate-term
      carrier
      '(x y)
      (putnam-1997-a4-carrier-term carrier op-xy)))))

(defun putnam-1997-a4-inverse-closure-function (carrier inv)
  (list
   'lambda
   '(x)
   (putnam-1997-a4-restricted-predicate-term
    carrier
    '(x)
    (putnam-1997-a4-carrier-term
     carrier
     (putnam-1997-a4-inverse-term inv 'x)))))

(defun putnam-1997-a4-associative-function (carrier op)
  (let* ((op-xy
          (putnam-1997-a4-operation-term op 'x 'y))
         (op-yz
          (putnam-1997-a4-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-1997-a4-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-1997-a4-operation-term op op-xy 'z)
       (putnam-1997-a4-operation-term op 'x op-yz))))))

(defun putnam-1997-a4-identity-function (carrier op one)
  (let ((left
         (list
          'equal
          (putnam-1997-a4-operation-term
           op (putnam-1997-a4-quoted one) 'x)
          'x))
        (right
         (list
          'equal
          (putnam-1997-a4-operation-term
           op 'x (putnam-1997-a4-quoted one))
          'x)))
    (list
     'lambda
     '(x)
     (putnam-1997-a4-restricted-predicate-term
      carrier
      '(x)
      (putnam-1997-a4-and-term left right)))))

(defun putnam-1997-a4-inverse-law-function
    (carrier op inv one)
  (let* ((inv-x
          (putnam-1997-a4-inverse-term inv 'x))
         (left
          (list
           'equal
           (putnam-1997-a4-operation-term op inv-x 'x)
           (putnam-1997-a4-quoted one)))
         (right
          (list
           'equal
           (putnam-1997-a4-operation-term op 'x inv-x)
           (putnam-1997-a4-quoted one))))
    (list
     'lambda
     '(x)
     (putnam-1997-a4-restricted-predicate-term
      carrier
      '(x)
      (putnam-1997-a4-and-term left right)))))

(defun putnam-1997-a4-phi-closure-function (carrier phi)
  (list
   'lambda
   '(x)
   (putnam-1997-a4-restricted-predicate-term
    carrier
    '(x)
    (putnam-1997-a4-carrier-term
     carrier
     (putnam-1997-a4-phi-term phi 'x)))))

(defun putnam-1997-a4-member-p (carrier element)
  (apply$ carrier (list element)))

(defun putnam-1997-a4-group-p (carrier op inv one)
  (and
   (tamep-functionp carrier)
   (tamep-functionp op)
   (tamep-functionp inv)
   (putnam-1997-a4-member-p carrier one)
   (fn-equal
    (putnam-1997-a4-operation-closure-function carrier op)
    (putnam-1997-a4-true-function '(x y)))
   (fn-equal
    (putnam-1997-a4-inverse-closure-function carrier inv)
    (putnam-1997-a4-true-function '(x)))
   (fn-equal
    (putnam-1997-a4-associative-function carrier op)
    (putnam-1997-a4-true-function '(x y z)))
   (fn-equal
    (putnam-1997-a4-identity-function carrier op one)
    (putnam-1997-a4-true-function '(x)))
   (fn-equal
    (putnam-1997-a4-inverse-law-function carrier op inv one)
    (putnam-1997-a4-true-function '(x)))))

(defun putnam-1997-a4-phi-closed-p (carrier phi)
  (and
   (tamep-functionp phi)
   (fn-equal
    (putnam-1997-a4-phi-closure-function carrier phi)
    (putnam-1997-a4-true-function '(x)))))

(defun putnam-1997-a4-triple-invariance-function
    (carrier op one phi)
  (let* ((g12
          (putnam-1997-a4-operation-term op 'g1 'g2))
         (g123
          (putnam-1997-a4-operation-term op g12 'g3))
         (h12
          (putnam-1997-a4-operation-term op 'h1 'h2))
         (h123
          (putnam-1997-a4-operation-term op h12 'h3))
         (phi-g1
          (putnam-1997-a4-phi-term phi 'g1))
         (phi-g2
          (putnam-1997-a4-phi-term phi 'g2))
         (phi-g3
          (putnam-1997-a4-phi-term phi 'g3))
         (phi-h1
          (putnam-1997-a4-phi-term phi 'h1))
         (phi-h2
          (putnam-1997-a4-phi-term phi 'h2))
         (phi-h3
          (putnam-1997-a4-phi-term phi 'h3))
         (phi-g12
          (putnam-1997-a4-operation-term
           op phi-g1 phi-g2))
         (phi-g123
          (putnam-1997-a4-operation-term
           op phi-g12 phi-g3))
         (phi-h12
          (putnam-1997-a4-operation-term
           op phi-h1 phi-h2))
         (phi-h123
          (putnam-1997-a4-operation-term
           op phi-h12 phi-h3))
         (both-products-one
          (putnam-1997-a4-and-term
           (list 'equal
                 g123
                 (putnam-1997-a4-quoted one))
           (list 'equal
                 h123
                 (putnam-1997-a4-quoted one)))))
    (list
     'lambda
     '(g1 g2 g3 h1 h2 h3)
     (putnam-1997-a4-restricted-predicate-term
      carrier
      '(g1 g2 g3 h1 h2 h3)
      (putnam-1997-a4-implies-term
       both-products-one
       (list 'equal phi-g123 phi-h123))))))

(defun putnam-1997-a4-triple-invariance-p
    (carrier op one phi)
  (fn-equal
   (putnam-1997-a4-triple-invariance-function
    carrier op one phi)
   (putnam-1997-a4-true-function
    '(g1 g2 g3 h1 h2 h3))))

;; If x |-> a*PHI(x) is a homomorphism, its value at the identity is the
;; identity, so necessarily a = inverse(PHI(one)). Thus the source existential
;; is equivalent to checking the following uniquely determined witness.

(defun putnam-1997-a4-homomorphism-function
    (carrier op inv one phi)
  (let* ((phi-one
          (putnam-1997-a4-phi-term
           phi (putnam-1997-a4-quoted one)))
         (a
          (putnam-1997-a4-inverse-term inv phi-one))
         (xy
          (putnam-1997-a4-operation-term op 'x 'y))
         (phi-xy
          (putnam-1997-a4-phi-term phi xy))
         (phi-x
          (putnam-1997-a4-phi-term phi 'x))
         (phi-y
          (putnam-1997-a4-phi-term phi 'y))
         (left
          (putnam-1997-a4-operation-term op a phi-xy))
         (translated-x
          (putnam-1997-a4-operation-term op a phi-x))
         (translated-y
          (putnam-1997-a4-operation-term op a phi-y))
         (right
          (putnam-1997-a4-operation-term
           op translated-x translated-y)))
    (list
     'lambda
     '(x y)
     (putnam-1997-a4-restricted-predicate-term
      carrier
      '(x y)
      (list 'equal left right)))))

(defun putnam-1997-a4-explicit-witness-homomorphism-p
    (carrier op inv one phi)
  (fn-equal
   (putnam-1997-a4-homomorphism-function
    carrier op inv one phi)
   (putnam-1997-a4-true-function '(x y))))

(defun putnambench-putnam-1997-a4-statement
    (carrier op inv one phi)
  (implies
   (and
    (putnam-1997-a4-group-p carrier op inv one)
    (putnam-1997-a4-phi-closed-p carrier phi)
    (putnam-1997-a4-triple-invariance-p
     carrier op one phi))
   (putnam-1997-a4-explicit-witness-homomorphism-p
    carrier op inv one phi)))

(value-triple :itpeval-statement-checked)
:q
