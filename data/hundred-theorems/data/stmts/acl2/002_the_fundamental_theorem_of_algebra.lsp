;; Statement-only formalization of hundred-theorems corpus artifact 002,
;; "The Fundamental Theorem of Algebra": every nonconstant polynomial over
;; the complex numbers has a complex root. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are presented as an arbitrary real closed ordered field. Complex
;; numbers are pairs of scalars, and univariate polynomials are finite
;; coefficient lists in ascending degree order. Real closed fields are
;; elementarily equivalent, so this first-order polynomial formulation is
;; equivalent to algebraic closedness of the usual complex numbers.
;;
;; FN-EQUAL against a constant-true function supplies unbounded universal
;; quantification. Its negation supplies the complex root existentially inside
;; the statement, rather than exposing a root or root selector as a parameter.
;; Every reified function uses only ACL2 primitives, loop scions, and APPLY$
;; calls on quoted tame functions. Finite Horner traces certify evaluation.

(defun ht002-quoted (object)
  (list 'quote object))

(defun ht002-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (ht002-term-list (cdr terms)))
    (ht002-quoted nil)))

(defun ht002-static-apply-term (function arguments)
  (list
   'apply$
   (ht002-quoted function)
   (ht002-term-list arguments)))

(defun ht002-index-range-term (last)
  (list
   'from-to-by
   (ht002-quoted 0)
   last
   (ht002-quoted 1)))

(defun ht002-apply1-term (function argument)
  (ht002-static-apply-term function (list argument)))

(defun ht002-apply2-term (function left right)
  (ht002-static-apply-term function (list left right)))

(defun ht002-and-term (terms)
  (if (endp terms)
      (ht002-quoted t)
    (list
     'if
     (car terms)
     (ht002-and-term (cdr terms))
     (ht002-quoted nil))))

(defun ht002-or-term (terms)
  (if (endp terms)
      (ht002-quoted nil)
    (list
     'if
     (car terms)
     (ht002-quoted t)
     (ht002-or-term (cdr terms)))))

(defun ht002-not-term (term)
  (list
   'if
   term
   (ht002-quoted nil)
   (ht002-quoted t)))

(defun ht002-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (ht002-quoted t)))

(defun ht002-true-function (formals)
  (list 'lambda formals (ht002-quoted t)))

(defun ht002-carrier-term (carrier element)
  (ht002-apply1-term carrier element))

(defun ht002-operation-term (operation left right)
  (ht002-apply2-term operation left right))

(defun ht002-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (ht002-quoted zero))
         (qone (ht002-quoted one))
         (add-xy (ht002-operation-term add x y))
         (add-yz (ht002-operation-term add y z))
         (mul-xy (ht002-operation-term mul x y))
         (mul-yz (ht002-operation-term mul y z))
         (neg-x (ht002-apply1-term neg x))
         (inv-x (ht002-apply1-term inv x))
         (domain
          (ht002-and-term
           (list
            (ht002-carrier-term carrier x)
            (ht002-carrier-term carrier y)
            (ht002-carrier-term carrier z))))
         (laws
          (ht002-and-term
           (list
            (ht002-carrier-term carrier add-xy)
            (ht002-carrier-term carrier mul-xy)
            (ht002-carrier-term carrier neg-x)
            (ht002-carrier-term carrier inv-x)
            (list
             'equal
             (ht002-operation-term add add-xy z)
             (ht002-operation-term add x add-yz))
            (list
             'equal
             (ht002-operation-term mul mul-xy z)
             (ht002-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (ht002-operation-term add y x))
            (list
             'equal
             mul-xy
             (ht002-operation-term mul y x))
            (list
             'equal
             (ht002-operation-term add x qzero)
             x)
            (list
             'equal
             (ht002-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (ht002-operation-term mul x qone)
             x)
            (ht002-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (ht002-implies-term
             (ht002-not-term (list 'equal x qzero))
             (list
              'equal
              (ht002-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (ht002-operation-term mul x add-yz)
             (ht002-operation-term
              add
              (ht002-operation-term mul x y)
              (ht002-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (ht002-implies-term domain laws))))

(defun ht002-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (ht002-quoted zero))
         (lt-xy (ht002-operation-term lt x y))
         (lt-yx (ht002-operation-term lt y x))
         (lt-yz (ht002-operation-term lt y z))
         (lt-xz (ht002-operation-term lt x z))
         (domain
          (ht002-and-term
           (list
            (ht002-carrier-term carrier x)
            (ht002-carrier-term carrier y)
            (ht002-carrier-term carrier z))))
         (laws
          (ht002-and-term
           (list
            (ht002-not-term
             (ht002-operation-term lt x x))
            (ht002-or-term
             (list lt-xy lt-yx (list 'equal x y)))
            (ht002-implies-term
             (ht002-and-term (list lt-xy lt-yz))
             lt-xz)
            (ht002-implies-term
             lt-xy
             (ht002-operation-term
              lt
              (ht002-operation-term add x z)
              (ht002-operation-term add y z)))
            (ht002-implies-term
             (ht002-and-term
              (list
               (ht002-operation-term lt qzero x)
               (ht002-operation-term lt qzero y)))
             (ht002-operation-term
              lt
              qzero
              (ht002-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (ht002-implies-term domain laws))))

(defun ht002-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (ht002-quoted zero))
         (root (ht002-apply1-term square-root x))
         (domain
          (ht002-and-term
           (list
            (ht002-carrier-term carrier x)
            (ht002-not-term
             (ht002-operation-term lt x qzero)))))
         (laws
          (ht002-and-term
           (list
            (ht002-carrier-term carrier root)
            (ht002-not-term
             (ht002-operation-term lt root qzero))
            (list
             'equal
             (ht002-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (ht002-implies-term domain laws))))

(defun ht002-real-root-trace-step-function (add mul)
  (let* ((coefficients (list 'car 'loop$-gvars))
         (root (list 'car (list 'cdr 'loop$-gvars)))
         (trace
          (list
           'car
           (list 'cdr (list 'cdr 'loop$-gvars))))
         (coefficient-index
          (list
           'binary-+
           (list
            'binary-+
            (list 'len coefficients)
            (ht002-quoted -1))
           (list 'unary-- 'loop$-ivars))))
    (list
     'lambda
     '(loop$-gvars loop$-ivars)
     (list
      'equal
      (list
       'nth
       (list
        'binary-+
        'loop$-ivars
        (ht002-quoted 1))
       trace)
      (ht002-static-apply-term
       add
       (list
        (list 'nth coefficient-index coefficients)
        (ht002-static-apply-term
         mul
         (list
          root
          (list 'nth 'loop$-ivars trace)))))))))

(defun ht002-odd-root-laws-function
    (carrier zero add mul odd-root)
  (let* ((coefficients 'coefficients)
         (witness (ht002-apply1-term odd-root coefficients))
         (root (list 'car witness))
         (trace (list 'car (list 'cdr witness)))
         (domain
          (ht002-and-term
           (list
            (list 'true-listp coefficients)
            (ht002-not-term
             (list
              '<
              (list 'len coefficients)
              (ht002-quoted 2)))
            (list
             'always$
             (ht002-quoted carrier)
             coefficients)
            (ht002-not-term
             (list
              'equal
              (list
               'nth
               (list
                'binary-+
                (list 'len coefficients)
                (ht002-quoted -1))
               coefficients)
              (ht002-quoted zero)))
            (list 'evenp (list 'len coefficients)))))
         (trace-law
          (list
           'always$+
           (ht002-quoted
            (ht002-real-root-trace-step-function add mul))
           (ht002-term-list
            (list coefficients root trace))
           (ht002-index-range-term
            (list
             'binary-+
             (list 'len coefficients)
             (ht002-quoted -1)))))
         (laws
          (ht002-and-term
           (list
            (list 'true-listp witness)
            (list
             'equal
             (list 'len witness)
             (ht002-quoted 2))
            (ht002-carrier-term carrier root)
            (list
             'equal
             (list 'len trace)
             (list
              'binary-+
              (list 'len coefficients)
              (ht002-quoted 1)))
            (list 'true-listp trace)
            (list
             'equal
             (list 'nth (ht002-quoted 0) trace)
             (ht002-quoted zero))
            trace-law
            (list
             'equal
             (list
              'nth
              (list 'len coefficients)
              trace)
             (ht002-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (ht002-implies-term domain laws))))

(defun ht002-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root)
  (let* ((field-laws
          (ht002-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (ht002-true-function '(x y z)))
         (order-laws
          (ht002-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (ht002-true-function '(x y z)))
         (square-root-laws
          (ht002-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (ht002-true-function '(x)))
         (odd-root-laws
          (ht002-odd-root-laws-function
           carrier zero add mul odd-root))
         (odd-root-laws-true
          (ht002-true-function '(coefficients))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp mul)
     (tamep-functionp neg)
     (tamep-functionp inv)
     (tamep-functionp lt)
     (tamep-functionp square-root)
     (tamep-functionp odd-root)
     (tamep-functionp field-laws)
     (tamep-functionp field-laws-true)
     (tamep-functionp order-laws)
     (tamep-functionp order-laws-true)
     (tamep-functionp square-root-laws)
     (tamep-functionp square-root-laws-true)
     (tamep-functionp odd-root-laws)
     (tamep-functionp odd-root-laws-true)
     (apply$ carrier (list zero))
     (apply$ carrier (list one))
     (not (equal zero one))
     (fn-equal field-laws field-laws-true)
     (fn-equal order-laws order-laws-true)
     (fn-equal square-root-laws square-root-laws-true)
     (fn-equal odd-root-laws odd-root-laws-true))))

(defun ht002-complex-p (z carrier)
  (and
   (consp z)
   (apply$ carrier (list (car z)))
   (apply$ carrier (list (cdr z)))))

(defun ht002-complex-zero (zero)
  (cons zero zero))

(defun ht002-complex-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (ht002-complex-p (car coefficients) carrier)
     (ht002-complex-coefficient-list-p
      (cdr coefficients) carrier))))

(defun ht002-positive-degree-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp (cdr coefficients))
   (ht002-complex-coefficient-list-p
    coefficients carrier)
   (not
    (equal
     (car (last coefficients))
     (ht002-complex-zero zero)))))

(defun ht002-complex-root-trace-step-function (add mul neg)
  (let* ((coefficients (list 'car 'loop$-gvars))
         (root (list 'car (list 'cdr 'loop$-gvars)))
         (trace
          (list
           'car
           (list 'cdr (list 'cdr 'loop$-gvars))))
         (coefficient-index
          (list
           'binary-+
           (list
            'binary-+
            (list 'len coefficients)
            (ht002-quoted -1))
           (list 'unary-- 'loop$-ivars)))
         (coefficient
          (list 'nth coefficient-index coefficients))
         (current (list 'nth 'loop$-ivars trace))
         (ac
          (ht002-static-apply-term
           mul
           (list (list 'car root) (list 'car current))))
         (bd
          (ht002-static-apply-term
           mul
           (list (list 'cdr root) (list 'cdr current))))
         (ad
          (ht002-static-apply-term
           mul
           (list (list 'car root) (list 'cdr current))))
         (bc
          (ht002-static-apply-term
           mul
           (list (list 'cdr root) (list 'car current))))
         (product-real
          (ht002-static-apply-term
           add
           (list
            ac
            (ht002-static-apply-term neg (list bd)))))
         (product-imaginary
          (ht002-static-apply-term add (list ad bc)))
         (next
          (list
           'cons
           (ht002-static-apply-term
            add
            (list (list 'car coefficient) product-real))
           (ht002-static-apply-term
            add
            (list (list 'cdr coefficient) product-imaginary)))))
    (list
     'lambda
     '(loop$-gvars loop$-ivars)
     (list
      'equal
      (list
       'nth
       (list
        'binary-+
        'loop$-ivars
        (ht002-quoted 1))
       trace)
      next))))

(defun ht002-root-failure-function
    (coefficients carrier zero add mul neg)
  (let* ((qcoefficients (ht002-quoted coefficients))
         (witness 'witness)
         (root (list 'car witness))
         (trace (list 'car (list 'cdr witness)))
         (complex-zero
          (list
           'cons
           (ht002-quoted zero)
           (ht002-quoted zero)))
         (trace-law
          (list
           'always$+
           (ht002-quoted
            (ht002-complex-root-trace-step-function
             add mul neg))
           (ht002-term-list
            (list qcoefficients root trace))
           (ht002-index-range-term
            (list
             'binary-+
             (list 'len qcoefficients)
             (ht002-quoted -1)))))
         (certificate
          (ht002-and-term
           (list
            (list 'true-listp witness)
            (list
             'equal
             (list 'len witness)
             (ht002-quoted 2))
            (list 'consp root)
            (ht002-carrier-term carrier (list 'car root))
            (ht002-carrier-term carrier (list 'cdr root))
            (list 'true-listp trace)
            (list
             'equal
             (list 'len trace)
             (list
              'binary-+
              (list 'len qcoefficients)
              (ht002-quoted 1)))
            (list
             'equal
             (list 'nth (ht002-quoted 0) trace)
             complex-zero)
            trace-law
            (list
             'equal
             (list 'nth (list 'len qcoefficients) trace)
             complex-zero)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      certificate
      (ht002-quoted nil)
      (ht002-quoted t)))))

(defun ht002-polynomial-has-root-p
    (coefficients carrier zero add mul neg)
  (let ((failure
         (ht002-root-failure-function
          coefficients carrier zero add mul neg))
        (always-true
         (ht002-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun hundred-theorems-002-fundamental-theorem-of-algebra-statement
    (carrier zero one add mul neg inv lt square-root odd-root coefficients)
  (implies
   (and
    (ht002-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root)
    (ht002-positive-degree-polynomial-p
     coefficients carrier zero))
   (ht002-polynomial-has-root-p
    coefficients carrier zero add mul neg)))

;; Admission-time tameness audit. Failure aborts before the statement sentinel.

(defun ht002-all-reified-functions-tame-p ()
  (let ((unary '(lambda (x) (quote t)))
        (binary '(lambda (x y) x)))
    (and
     (tamep-functionp unary)
     (tamep-functionp binary)
     (tamep-functionp
      (ht002-true-function '(x y z)))
     (tamep-functionp
      (ht002-true-function '(x)))
     (tamep-functionp
      (ht002-true-function '(coefficients)))
     (tamep-functionp
      (ht002-true-function '(witness)))
     (tamep-functionp
      (ht002-field-laws-function
       unary 0 1 binary binary unary unary))
     (tamep-functionp
      (ht002-order-laws-function
       unary 0 binary binary binary))
     (tamep-functionp
      (ht002-square-root-laws-function
       unary 0 binary binary unary))
     (tamep-functionp
      (ht002-real-root-trace-step-function binary binary))
     (tamep-functionp
      (ht002-odd-root-laws-function
       unary 0 binary binary unary))
     (tamep-functionp
      (ht002-complex-root-trace-step-function
       binary binary unary))
     (tamep-functionp
      (ht002-root-failure-function
       nil unary 0 binary binary unary)))))

(value-triple
 (if (ht002-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'ht002-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
