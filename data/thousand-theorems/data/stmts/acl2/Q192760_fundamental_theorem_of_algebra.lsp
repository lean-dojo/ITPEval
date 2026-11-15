;; Statement-only formalization of thousand-theorems corpus artifact Q192760,
;; "Fundamental theorem of algebra": every nonconstant polynomial over the
;; complex numbers has a complex root. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are presented as an arbitrary real closed ordered field. Complex
;; numbers are pairs of scalars, and univariate polynomials are finite
;; coefficient lists in ascending degree order. An ordered field is real
;; closed exactly when its complexification is algebraically closed; thus this
;; is a bidirectionally equivalent first-order rendering of
;; Complex.isAlgClosed for the usual complex numbers.
;;
;; FN-EQUAL against a constant-true function supplies unbounded universal
;; quantification. Its negation supplies the complex root existentially inside
;; the statement, rather than exposing a root or root selector as a parameter.
;; Every reified function uses only ACL2 primitives, loop scions, and APPLY$
;; calls on quoted tame functions. Finite Horner traces certify evaluation.

(defun q192760-quoted (object)
  (list 'quote object))

(defun q192760-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q192760-term-list (cdr terms)))
    (q192760-quoted nil)))

(defun q192760-static-apply-term (function arguments)
  (list
   'apply$
   (q192760-quoted function)
   (q192760-term-list arguments)))

(defun q192760-index-range-term (last)
  (list
   'from-to-by
   (q192760-quoted 0)
   last
   (q192760-quoted 1)))

(defun q192760-apply1-term (function argument)
  (q192760-static-apply-term function (list argument)))

(defun q192760-apply2-term (function left right)
  (q192760-static-apply-term function (list left right)))

(defun q192760-and-term (terms)
  (if (endp terms)
      (q192760-quoted t)
    (list
     'if
     (car terms)
     (q192760-and-term (cdr terms))
     (q192760-quoted nil))))

(defun q192760-or-term (terms)
  (if (endp terms)
      (q192760-quoted nil)
    (list
     'if
     (car terms)
     (q192760-quoted t)
     (q192760-or-term (cdr terms)))))

(defun q192760-not-term (term)
  (list
   'if
   term
   (q192760-quoted nil)
   (q192760-quoted t)))

(defun q192760-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (q192760-quoted t)))

(defun q192760-true-function (formals)
  (list 'lambda formals (q192760-quoted t)))

(defun q192760-carrier-term (carrier element)
  (q192760-apply1-term carrier element))

(defun q192760-operation-term (operation left right)
  (q192760-apply2-term operation left right))

(defun q192760-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (q192760-quoted zero))
         (qone (q192760-quoted one))
         (add-xy (q192760-operation-term add x y))
         (add-yz (q192760-operation-term add y z))
         (mul-xy (q192760-operation-term mul x y))
         (mul-yz (q192760-operation-term mul y z))
         (neg-x (q192760-apply1-term neg x))
         (inv-x (q192760-apply1-term inv x))
         (domain
          (q192760-and-term
           (list
            (q192760-carrier-term carrier x)
            (q192760-carrier-term carrier y)
            (q192760-carrier-term carrier z))))
         (laws
          (q192760-and-term
           (list
            (q192760-carrier-term carrier add-xy)
            (q192760-carrier-term carrier mul-xy)
            (q192760-carrier-term carrier neg-x)
            (q192760-carrier-term carrier inv-x)
            (list
             'equal
             (q192760-operation-term add add-xy z)
             (q192760-operation-term add x add-yz))
            (list
             'equal
             (q192760-operation-term mul mul-xy z)
             (q192760-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (q192760-operation-term add y x))
            (list
             'equal
             mul-xy
             (q192760-operation-term mul y x))
            (list
             'equal
             (q192760-operation-term add x qzero)
             x)
            (list
             'equal
             (q192760-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (q192760-operation-term mul x qone)
             x)
            (q192760-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (q192760-implies-term
             (q192760-not-term (list 'equal x qzero))
             (list
              'equal
              (q192760-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (q192760-operation-term mul x add-yz)
             (q192760-operation-term
              add
              (q192760-operation-term mul x y)
              (q192760-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (q192760-implies-term domain laws))))

(defun q192760-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (q192760-quoted zero))
         (lt-xy (q192760-operation-term lt x y))
         (lt-yx (q192760-operation-term lt y x))
         (lt-yz (q192760-operation-term lt y z))
         (lt-xz (q192760-operation-term lt x z))
         (domain
          (q192760-and-term
           (list
            (q192760-carrier-term carrier x)
            (q192760-carrier-term carrier y)
            (q192760-carrier-term carrier z))))
         (laws
          (q192760-and-term
           (list
            (q192760-not-term
             (q192760-operation-term lt x x))
            (q192760-or-term
             (list lt-xy lt-yx (list 'equal x y)))
            (q192760-implies-term
             (q192760-and-term (list lt-xy lt-yz))
             lt-xz)
            (q192760-implies-term
             lt-xy
             (q192760-operation-term
              lt
              (q192760-operation-term add x z)
              (q192760-operation-term add y z)))
            (q192760-implies-term
             (q192760-and-term
              (list
               (q192760-operation-term lt qzero x)
               (q192760-operation-term lt qzero y)))
             (q192760-operation-term
              lt
              qzero
              (q192760-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (q192760-implies-term domain laws))))

(defun q192760-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (q192760-quoted zero))
         (root (q192760-apply1-term square-root x))
         (domain
          (q192760-and-term
           (list
            (q192760-carrier-term carrier x)
            (q192760-not-term
             (q192760-operation-term lt x qzero)))))
         (laws
          (q192760-and-term
           (list
            (q192760-carrier-term carrier root)
            (q192760-not-term
             (q192760-operation-term lt root qzero))
            (list
             'equal
             (q192760-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (q192760-implies-term domain laws))))

(defun q192760-real-root-trace-step-function (add mul)
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
            (q192760-quoted -1))
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
        (q192760-quoted 1))
       trace)
      (q192760-static-apply-term
       add
       (list
        (list 'nth coefficient-index coefficients)
        (q192760-static-apply-term
         mul
         (list
          root
          (list 'nth 'loop$-ivars trace)))))))))

(defun q192760-odd-root-laws-function
    (carrier zero add mul odd-root)
  (let* ((coefficients 'coefficients)
         (witness (q192760-apply1-term odd-root coefficients))
         (root (list 'car witness))
         (trace (list 'car (list 'cdr witness)))
         (domain
          (q192760-and-term
           (list
            (list 'true-listp coefficients)
            (q192760-not-term
             (list
              '<
              (list 'len coefficients)
              (q192760-quoted 2)))
            (list
             'always$
             (q192760-quoted carrier)
             coefficients)
            (q192760-not-term
             (list
              'equal
              (list
               'nth
               (list
                'binary-+
                (list 'len coefficients)
                (q192760-quoted -1))
               coefficients)
              (q192760-quoted zero)))
            (list 'evenp (list 'len coefficients)))))
         (trace-law
          (list
           'always$+
           (q192760-quoted
            (q192760-real-root-trace-step-function add mul))
           (q192760-term-list
            (list coefficients root trace))
           (q192760-index-range-term
            (list
             'binary-+
             (list 'len coefficients)
             (q192760-quoted -1)))))
         (laws
          (q192760-and-term
           (list
            (list 'true-listp witness)
            (list
             'equal
             (list 'len witness)
             (q192760-quoted 2))
            (q192760-carrier-term carrier root)
            (list
             'equal
             (list 'len trace)
             (list
              'binary-+
              (list 'len coefficients)
              (q192760-quoted 1)))
            (list 'true-listp trace)
            (list
             'equal
             (list 'nth (q192760-quoted 0) trace)
             (q192760-quoted zero))
            trace-law
            (list
             'equal
             (list
              'nth
              (list 'len coefficients)
              trace)
             (q192760-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (q192760-implies-term domain laws))))

(defun q192760-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root)
  (let* ((field-laws
          (q192760-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (q192760-true-function '(x y z)))
         (order-laws
          (q192760-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (q192760-true-function '(x y z)))
         (square-root-laws
          (q192760-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (q192760-true-function '(x)))
         (odd-root-laws
          (q192760-odd-root-laws-function
           carrier zero add mul odd-root))
         (odd-root-laws-true
          (q192760-true-function '(coefficients))))
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

(defun q192760-complex-p (z carrier)
  (and
   (consp z)
   (apply$ carrier (list (car z)))
   (apply$ carrier (list (cdr z)))))

(defun q192760-complex-zero (zero)
  (cons zero zero))

(defun q192760-complex-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (q192760-complex-p (car coefficients) carrier)
     (q192760-complex-coefficient-list-p
      (cdr coefficients) carrier))))

(defun q192760-positive-degree-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp (cdr coefficients))
   (q192760-complex-coefficient-list-p
    coefficients carrier)
   (not
    (equal
     (car (last coefficients))
     (q192760-complex-zero zero)))))

(defun q192760-complex-root-trace-step-function (add mul neg)
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
            (q192760-quoted -1))
           (list 'unary-- 'loop$-ivars)))
         (coefficient
          (list 'nth coefficient-index coefficients))
         (current (list 'nth 'loop$-ivars trace))
         (ac
          (q192760-static-apply-term
           mul
           (list (list 'car root) (list 'car current))))
         (bd
          (q192760-static-apply-term
           mul
           (list (list 'cdr root) (list 'cdr current))))
         (ad
          (q192760-static-apply-term
           mul
           (list (list 'car root) (list 'cdr current))))
         (bc
          (q192760-static-apply-term
           mul
           (list (list 'cdr root) (list 'car current))))
         (product-real
          (q192760-static-apply-term
           add
           (list
            ac
            (q192760-static-apply-term neg (list bd)))))
         (product-imaginary
          (q192760-static-apply-term add (list ad bc)))
         (next
          (list
           'cons
           (q192760-static-apply-term
            add
            (list (list 'car coefficient) product-real))
           (q192760-static-apply-term
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
        (q192760-quoted 1))
       trace)
      next))))

(defun q192760-root-failure-function
    (coefficients carrier zero add mul neg)
  (let* ((qcoefficients (q192760-quoted coefficients))
         (witness 'witness)
         (root (list 'car witness))
         (trace (list 'car (list 'cdr witness)))
         (complex-zero
          (list
           'cons
           (q192760-quoted zero)
           (q192760-quoted zero)))
         (trace-law
          (list
           'always$+
           (q192760-quoted
            (q192760-complex-root-trace-step-function
             add mul neg))
           (q192760-term-list
            (list qcoefficients root trace))
           (q192760-index-range-term
            (list
             'binary-+
             (list 'len qcoefficients)
             (q192760-quoted -1)))))
         (certificate
          (q192760-and-term
           (list
            (list 'true-listp witness)
            (list
             'equal
             (list 'len witness)
             (q192760-quoted 2))
            (list 'consp root)
            (q192760-carrier-term carrier (list 'car root))
            (q192760-carrier-term carrier (list 'cdr root))
            (list 'true-listp trace)
            (list
             'equal
             (list 'len trace)
             (list
              'binary-+
              (list 'len qcoefficients)
              (q192760-quoted 1)))
            (list
             'equal
             (list 'nth (q192760-quoted 0) trace)
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
      (q192760-quoted nil)
      (q192760-quoted t)))))

(defun q192760-polynomial-has-root-p
    (coefficients carrier zero add mul neg)
  (let ((failure
         (q192760-root-failure-function
          coefficients carrier zero add mul neg))
        (always-true
         (q192760-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun thousand-theorems-q192760-fundamental-theorem-of-algebra-statement
    (carrier zero one add mul neg inv lt square-root odd-root coefficients)
  (implies
   (and
    (q192760-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root)
    (q192760-positive-degree-polynomial-p
     coefficients carrier zero))
   (q192760-polynomial-has-root-p
    coefficients carrier zero add mul neg)))

;; Admission-time tameness audit. Failure aborts before the statement sentinel.

(defun q192760-all-reified-functions-tame-p ()
  (let ((unary '(lambda (x) (quote t)))
        (binary '(lambda (x y) x)))
    (and
     (tamep-functionp unary)
     (tamep-functionp binary)
     (tamep-functionp
      (q192760-true-function '(x y z)))
     (tamep-functionp
      (q192760-true-function '(x)))
     (tamep-functionp
      (q192760-true-function '(coefficients)))
     (tamep-functionp
      (q192760-true-function '(witness)))
     (tamep-functionp
      (q192760-field-laws-function
       unary 0 1 binary binary unary unary))
     (tamep-functionp
      (q192760-order-laws-function
       unary 0 binary binary binary))
     (tamep-functionp
      (q192760-square-root-laws-function
       unary 0 binary binary unary))
     (tamep-functionp
      (q192760-real-root-trace-step-function binary binary))
     (tamep-functionp
      (q192760-odd-root-laws-function
       unary 0 binary binary unary))
     (tamep-functionp
      (q192760-complex-root-trace-step-function
       binary binary unary))
     (tamep-functionp
      (q192760-root-failure-function
       nil unary 0 binary binary unary)))))

(value-triple
 (if (q192760-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q192760-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
