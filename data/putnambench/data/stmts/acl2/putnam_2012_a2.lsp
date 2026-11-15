;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_a2:
;; cancellation in a commutative semigroup whose left translations are
;; surjective. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; CARRIER is an ACL2 function object. OPERATION-PACKAGE is the pair consisting
;; of the source binary operation and a right-solver function. Its universal
;; law says that for every carrier x and y, the solver returns a carrier z with
;; OP(x,z)=y. Forgetting the solver gives the source condition
;; forall x y, exists z; conversely, classical choice equips every source
;; operation satisfying that condition with such a solver. Thus this bundled
;; representation is bidirectionally equivalent and does not expose the
;; existential witness as a separate statement parameter. FN-EQUAL against a
;; constant-T function supplies the unbounded universal quantifiers.

(defun putnam-2012-a2-quoted (object)
  (list 'quote object))

(defun putnam-2012-a2-apply1-term (function argument)
  (list
   'apply$
   (putnam-2012-a2-quoted function)
   (list 'cons argument nil)))

(defun putnam-2012-a2-apply2-term (function left right)
  (list
   'apply$
   (putnam-2012-a2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2012-a2-carrier-term (carrier element)
  (putnam-2012-a2-apply1-term carrier element))

(defun putnam-2012-a2-operation-term (operation left right)
  (putnam-2012-a2-apply2-term operation left right))

(defun putnam-2012-a2-and-term (terms)
  (if (endp terms)
      (putnam-2012-a2-quoted t)
    (list
     'if
     (car terms)
     (putnam-2012-a2-and-term (cdr terms))
     (putnam-2012-a2-quoted nil))))

(defun putnam-2012-a2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2012-a2-quoted t)))

(defun putnam-2012-a2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2012-a2-quoted t)))

(defun putnam-2012-a2-binary-laws-function (carrier operation)
  (let* ((x 'x)
         (y 'y)
         (op-xy
          (putnam-2012-a2-operation-term operation x y))
         (domain
          (putnam-2012-a2-and-term
           (list
            (putnam-2012-a2-carrier-term carrier x)
            (putnam-2012-a2-carrier-term carrier y))))
         (laws
          (putnam-2012-a2-and-term
           (list
            (putnam-2012-a2-carrier-term carrier op-xy)
            (list
             'equal
             op-xy
             (putnam-2012-a2-operation-term operation y x))))))
    (list
     'lambda
     '(x y)
     (putnam-2012-a2-implies-term domain laws))))

(defun putnam-2012-a2-associative-law-function (carrier operation)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (domain
          (putnam-2012-a2-and-term
           (list
            (putnam-2012-a2-carrier-term carrier x)
            (putnam-2012-a2-carrier-term carrier y)
            (putnam-2012-a2-carrier-term carrier z))))
         (law
          (list
           'equal
           (putnam-2012-a2-operation-term
            operation
            x
            (putnam-2012-a2-operation-term operation y z))
           (putnam-2012-a2-operation-term
            operation
            (putnam-2012-a2-operation-term operation x y)
            z))))
    (list
     'lambda
     '(x y z)
     (putnam-2012-a2-implies-term domain law))))

(defun putnam-2012-a2-surjectivity-function
    (carrier operation solver)
  (let* ((x 'x)
         (y 'y)
         (z
          (putnam-2012-a2-operation-term solver x y))
         (domain
          (putnam-2012-a2-and-term
           (list
            (putnam-2012-a2-carrier-term carrier x)
            (putnam-2012-a2-carrier-term carrier y))))
         (law
          (putnam-2012-a2-and-term
           (list
            (putnam-2012-a2-carrier-term carrier z)
            (list
             'equal
             (putnam-2012-a2-operation-term operation x z)
             y)))))
    (list
     'lambda
     '(x y)
     (putnam-2012-a2-implies-term domain law))))

(defun putnam-2012-a2-op (operation x y)
  (apply$ operation (list x y)))

(defun putnambench-putnam-2012-a2-statement
    (carrier operation-package a b c)
  (let ((operation (car operation-package))
        (solver (cadr operation-package)))
    (implies
     (and
      (true-listp operation-package)
      (equal (len operation-package) 2)
      (tamep-functionp carrier)
      (tamep-functionp operation)
      (tamep-functionp solver)
      (apply$ carrier (list a))
      (apply$ carrier (list b))
      (apply$ carrier (list c))
      (fn-equal
       (putnam-2012-a2-binary-laws-function carrier operation)
       (putnam-2012-a2-true-function '(x y)))
      (fn-equal
       (putnam-2012-a2-associative-law-function carrier operation)
       (putnam-2012-a2-true-function '(x y z)))
      (fn-equal
       (putnam-2012-a2-surjectivity-function
        carrier operation solver)
       (putnam-2012-a2-true-function '(x y)))
      (equal
       (putnam-2012-a2-op operation a c)
       (putnam-2012-a2-op operation b c)))
     (equal a b))))

;; The generated surjectivity lambda uses only tame ACL2 primitives and APPLY$
;; on quoted tame function objects; in particular it contains no unwarranted
;; custom function call.
(value-triple
 (list
  :itpeval-tame-surjectivity
  (tamep-functionp
   (putnam-2012-a2-surjectivity-function
    '(lambda (x) (quote t))
    '(lambda (x y) x)
    '(lambda (x y) y)))))

(value-triple :itpeval-statement-checked)
:q
