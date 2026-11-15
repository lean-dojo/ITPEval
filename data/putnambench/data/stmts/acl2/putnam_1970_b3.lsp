;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_b3:
;; a closed subset of the real plane contained in a bounded vertical strip
;; has closed projection onto the y-axis. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ objects present an arbitrary Dedekind-complete ordered field,
;; hence a copy of the real field, and arbitrary predicates on it. FN-EQUAL
;; supplies unbounded universal quantification; inequality with a constant
;; false function supplies internal existential witnesses. Closedness is
;; expanded using the exact order topology and its product-rectangle basis.

(defun putnam-1970-b3-quoted (object)
  (list 'quote object))

(defun putnam-1970-b3-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1970-b3-term-list (cdr terms)))
    (putnam-1970-b3-quoted nil)))

(defun putnam-1970-b3-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (putnam-1970-b3-term-list arguments)))

(defun putnam-1970-b3-static-apply-term (function arguments)
  (putnam-1970-b3-apply-term
   (putnam-1970-b3-quoted function)
   arguments))

(defun putnam-1970-b3-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1970-b3-and-terms (cdr terms))
            (putnam-1970-b3-quoted nil))
    (putnam-1970-b3-quoted t)))

(defun putnam-1970-b3-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1970-b3-quoted t)
            (putnam-1970-b3-or-terms (cdr terms)))
    (putnam-1970-b3-quoted nil)))

(defun putnam-1970-b3-not-term (term)
  (list 'if term
        (putnam-1970-b3-quoted nil)
        (putnam-1970-b3-quoted t)))

(defun putnam-1970-b3-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (putnam-1970-b3-quoted t)))

(defun putnam-1970-b3-true-function (formals)
  (list 'lambda formals (putnam-1970-b3-quoted t)))

(defun putnam-1970-b3-false-function (formals)
  (list 'lambda formals (putnam-1970-b3-quoted nil)))

(defun putnam-1970-b3-universal-p (function formals)
  (let ((always-true
         (putnam-1970-b3-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun putnam-1970-b3-exists-p (function formals)
  (let ((always-false
         (putnam-1970-b3-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun putnam-1970-b3-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun putnam-1970-b3-binary-value (function left right)
  (apply$ function (list left right)))

;; Arbitrary subsets of a represented carrier.

(defun putnam-1970-b3-set-subset-function
    (carrier left right)
  (list
   'lambda '(x)
   (putnam-1970-b3-implies-term
    (putnam-1970-b3-and-terms
     (list
      (putnam-1970-b3-static-apply-term carrier '(x))
      (putnam-1970-b3-static-apply-term left '(x))))
    (putnam-1970-b3-static-apply-term right '(x)))))

(defun putnam-1970-b3-set-subset-p
    (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-set-subset-function
     carrier left right)
    '(x))))

(defun putnam-1970-b3-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (putnam-1970-b3-set-subset-p carrier set carrier)))

(defun putnam-1970-b3-complement-set (carrier set)
  (list
   'lambda '(x)
   (putnam-1970-b3-and-terms
    (list
     (putnam-1970-b3-static-apply-term carrier '(x))
     (putnam-1970-b3-not-term
      (putnam-1970-b3-static-apply-term set '(x)))))))

;; A Dedekind-complete ordered field is an abstract presentation of R.

(defun putnam-1970-b3-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add
          (putnam-1970-b3-static-apply-term add '(x y)))
         (yz-add
          (putnam-1970-b3-static-apply-term add '(y z)))
         (xy-mul
          (putnam-1970-b3-static-apply-term multiply '(x y)))
         (yz-mul
          (putnam-1970-b3-static-apply-term multiply '(y z)))
         (neg-x
          (putnam-1970-b3-static-apply-term negate '(x)))
         (inv-x
          (putnam-1970-b3-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (putnam-1970-b3-implies-term
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-static-apply-term carrier '(x))
        (putnam-1970-b3-static-apply-term carrier '(y))
        (putnam-1970-b3-static-apply-term carrier '(z))))
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-static-apply-term carrier (list xy-add))
        (putnam-1970-b3-static-apply-term carrier (list xy-mul))
        (putnam-1970-b3-static-apply-term carrier (list neg-x))
        (putnam-1970-b3-static-apply-term carrier (list inv-x))
        (list
         'equal
         (putnam-1970-b3-static-apply-term add (list xy-add 'z))
         (putnam-1970-b3-static-apply-term add (list 'x yz-add)))
        (list
         'equal
         xy-add
         (putnam-1970-b3-static-apply-term add '(y x)))
        (list
         'equal
         (putnam-1970-b3-static-apply-term
          add (list 'x (putnam-1970-b3-quoted zero)))
         'x)
        (list
         'equal
         (putnam-1970-b3-static-apply-term add (list 'x neg-x))
         (putnam-1970-b3-quoted zero))
        (list
         'equal
         (putnam-1970-b3-static-apply-term
          multiply (list xy-mul 'z))
         (putnam-1970-b3-static-apply-term
          multiply (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (putnam-1970-b3-static-apply-term multiply '(y x)))
        (list
         'equal
         (putnam-1970-b3-static-apply-term
          multiply (list 'x (putnam-1970-b3-quoted one)))
         'x)
        (putnam-1970-b3-implies-term
         (list 'equal 'x (putnam-1970-b3-quoted zero))
         (list 'equal inv-x (putnam-1970-b3-quoted zero)))
        (putnam-1970-b3-implies-term
         (putnam-1970-b3-not-term
          (list 'equal 'x (putnam-1970-b3-quoted zero)))
         (list
          'equal
          (putnam-1970-b3-static-apply-term
           multiply (list 'x inv-x))
          (putnam-1970-b3-quoted one)))
        (list
         'equal
         (putnam-1970-b3-static-apply-term
          multiply (list 'x yz-add))
         (putnam-1970-b3-static-apply-term
          add
          (list
           (putnam-1970-b3-static-apply-term multiply '(x y))
           (putnam-1970-b3-static-apply-term
            multiply '(x z)))))))))))

(defun putnam-1970-b3-order-laws-function
    (carrier zero add multiply less)
  (let ((xy
         (putnam-1970-b3-static-apply-term less '(x y)))
        (yx
         (putnam-1970-b3-static-apply-term less '(y x)))
        (yz
         (putnam-1970-b3-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (putnam-1970-b3-implies-term
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-static-apply-term carrier '(x))
        (putnam-1970-b3-static-apply-term carrier '(y))
        (putnam-1970-b3-static-apply-term carrier '(z))))
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-not-term
         (putnam-1970-b3-static-apply-term less '(x x)))
        (putnam-1970-b3-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (putnam-1970-b3-implies-term
         (putnam-1970-b3-and-terms (list xy yz))
         (putnam-1970-b3-static-apply-term less '(x z)))
        (putnam-1970-b3-implies-term
         xy
         (putnam-1970-b3-static-apply-term
          less
          (list
           (putnam-1970-b3-static-apply-term add '(x z))
           (putnam-1970-b3-static-apply-term add '(y z)))))
        (putnam-1970-b3-implies-term
         (putnam-1970-b3-and-terms
          (list
           (putnam-1970-b3-static-apply-term
            less (list (putnam-1970-b3-quoted zero) 'x))
           (putnam-1970-b3-static-apply-term
            less (list (putnam-1970-b3-quoted zero) 'y))))
         (putnam-1970-b3-static-apply-term
          less
          (list
           (putnam-1970-b3-quoted zero)
           (putnam-1970-b3-static-apply-term
            multiply '(x y)))))))))))

(defun putnam-1970-b3-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (putnam-1970-b3-implies-term
    (putnam-1970-b3-and-terms
     (list
      (putnam-1970-b3-static-apply-term carrier '(x))
      (putnam-1970-b3-static-apply-term set '(x))))
    (putnam-1970-b3-not-term
     (putnam-1970-b3-static-apply-term
      less (list (putnam-1970-b3-quoted upper) 'x))))))

(defun putnam-1970-b3-upper-bound-p
    (carrier less set upper)
  (and
   (putnam-1970-b3-member-p carrier upper)
   (putnam-1970-b3-valid-set-p carrier set)
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-upper-bound-function
     carrier less set upper)
    '(x))))

(defun putnam-1970-b3-set-nonempty-function
    (carrier set)
  (list
   'lambda '(x)
   (putnam-1970-b3-and-terms
    (list
     (putnam-1970-b3-static-apply-term carrier '(x))
     (putnam-1970-b3-static-apply-term set '(x))))))

(defun putnam-1970-b3-set-nonempty-p (carrier set)
  (and
   (putnam-1970-b3-valid-set-p carrier set)
   (putnam-1970-b3-exists-p
    (putnam-1970-b3-set-nonempty-function carrier set)
    '(x))))

(defun putnam-1970-b3-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list
    'putnam-1970-b3-upper-bound-p
    (putnam-1970-b3-quoted carrier)
    (putnam-1970-b3-quoted less)
    (putnam-1970-b3-quoted set)
    'upper)))

(defun putnam-1970-b3-bounded-above-p
    (carrier less set)
  (putnam-1970-b3-exists-p
   (putnam-1970-b3-bounded-above-function
    carrier less set)
   '(upper)))

(defun putnam-1970-b3-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (putnam-1970-b3-implies-term
    (list
     'putnam-1970-b3-upper-bound-p
     (putnam-1970-b3-quoted carrier)
     (putnam-1970-b3-quoted less)
     (putnam-1970-b3-quoted set)
     'upper)
    (putnam-1970-b3-not-term
     (putnam-1970-b3-static-apply-term
      less (list 'upper (putnam-1970-b3-quoted supremum)))))))

(defun putnam-1970-b3-least-upper-bound-p
    (carrier less set supremum)
  (and
   (putnam-1970-b3-upper-bound-p
    carrier less set supremum)
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun putnam-1970-b3-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (putnam-1970-b3-implies-term
    (putnam-1970-b3-and-terms
     (list
      (list
       'putnam-1970-b3-valid-set-p
       (putnam-1970-b3-quoted carrier)
       'set)
      (list
       'putnam-1970-b3-set-nonempty-p
       (putnam-1970-b3-quoted carrier)
       'set)
      (list
       'putnam-1970-b3-bounded-above-p
       (putnam-1970-b3-quoted carrier)
       (putnam-1970-b3-quoted less)
       'set)))
    (list
     'putnam-1970-b3-least-upper-bound-p
     (putnam-1970-b3-quoted carrier)
     (putnam-1970-b3-quoted less)
     'set
     (putnam-1970-b3-static-apply-term
      supremum-operation '(set))))))

(defun putnam-1970-b3-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (putnam-1970-b3-member-p carrier zero)
   (putnam-1970-b3-member-p carrier one)
   (not (equal zero one))
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-completeness-function
     carrier less supremum)
    '(set))
   (putnam-1970-b3-binary-value less zero one)))

;; Real-field context.

(defun putnam-1970-b3-r-carrier (ctx) (nth 0 ctx))
(defun putnam-1970-b3-r-zero (ctx) (nth 1 ctx))
(defun putnam-1970-b3-r-one (ctx) (nth 2 ctx))
(defun putnam-1970-b3-r-add (ctx) (nth 3 ctx))
(defun putnam-1970-b3-r-multiply (ctx) (nth 4 ctx))
(defun putnam-1970-b3-r-negate (ctx) (nth 5 ctx))
(defun putnam-1970-b3-r-inverse (ctx) (nth 6 ctx))
(defun putnam-1970-b3-r-less (ctx) (nth 7 ctx))
(defun putnam-1970-b3-r-supremum (ctx) (nth 8 ctx))

(defun putnam-1970-b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (putnam-1970-b3-real-field-p
    (putnam-1970-b3-r-carrier ctx)
    (putnam-1970-b3-r-zero ctx)
    (putnam-1970-b3-r-one ctx)
    (putnam-1970-b3-r-add ctx)
    (putnam-1970-b3-r-multiply ctx)
    (putnam-1970-b3-r-negate ctx)
    (putnam-1970-b3-r-inverse ctx)
    (putnam-1970-b3-r-less ctx)
    (putnam-1970-b3-r-supremum ctx))))

;; The exact order topology on the represented real field.

(defun putnam-1970-b3-open-interval-subset-function
    (carrier less lower upper set)
  (list
   'lambda '(y)
   (putnam-1970-b3-implies-term
    (putnam-1970-b3-and-terms
     (list
      (putnam-1970-b3-static-apply-term carrier '(y))
      (putnam-1970-b3-static-apply-term
       less (list (putnam-1970-b3-quoted lower) 'y))
      (putnam-1970-b3-static-apply-term
       less (list 'y (putnam-1970-b3-quoted upper)))))
    (putnam-1970-b3-static-apply-term set '(y)))))

(defun putnam-1970-b3-open-interval-subset-p
    (carrier less lower upper set)
  (putnam-1970-b3-universal-p
   (putnam-1970-b3-open-interval-subset-function
    carrier less lower upper set)
   '(y)))

(defun putnam-1970-b3-order-neighborhood-witness-function
    (carrier less set x)
  (list
   'lambda '(bounds)
   (putnam-1970-b3-and-terms
    (list
     (list 'true-listp 'bounds)
     (list 'equal (list 'len 'bounds) (putnam-1970-b3-quoted 2))
     (putnam-1970-b3-static-apply-term
      carrier (list (list 'car 'bounds)))
     (putnam-1970-b3-static-apply-term
      carrier (list (list 'cadr 'bounds)))
     (putnam-1970-b3-static-apply-term
      less
      (list (list 'car 'bounds) (putnam-1970-b3-quoted x)))
     (putnam-1970-b3-static-apply-term
      less
      (list (putnam-1970-b3-quoted x) (list 'cadr 'bounds)))
     (list
      'putnam-1970-b3-open-interval-subset-p
      (putnam-1970-b3-quoted carrier)
      (putnam-1970-b3-quoted less)
      (list 'car 'bounds)
      (list 'cadr 'bounds)
      (putnam-1970-b3-quoted set))))))

(defun putnam-1970-b3-order-neighborhood-p
    (carrier less set x)
  (putnam-1970-b3-exists-p
   (putnam-1970-b3-order-neighborhood-witness-function
    carrier less set x)
   '(bounds)))

(defun putnam-1970-b3-order-open-points-function
    (carrier less set)
  (list
   'lambda '(x)
   (putnam-1970-b3-implies-term
    (putnam-1970-b3-and-terms
     (list
      (putnam-1970-b3-static-apply-term carrier '(x))
      (putnam-1970-b3-static-apply-term set '(x))))
    (list
     'putnam-1970-b3-order-neighborhood-p
     (putnam-1970-b3-quoted carrier)
     (putnam-1970-b3-quoted less)
     (putnam-1970-b3-quoted set)
     'x))))

(defun putnam-1970-b3-order-open-p
    (carrier less set)
  (and
   (putnam-1970-b3-valid-set-p carrier set)
   (putnam-1970-b3-universal-p
    (putnam-1970-b3-order-open-points-function
     carrier less set)
    '(x))))

(defun putnam-1970-b3-order-closed-p
    (carrier less set)
  (and
   (putnam-1970-b3-valid-set-p carrier set)
   (putnam-1970-b3-order-open-p
    carrier less
    (putnam-1970-b3-complement-set carrier set))))

;; Ordered pairs are dotted ACL2 pairs. Open rectangles give the product
;; topology on R x R.

(defun putnam-1970-b3-plane-carrier (carrier)
  (list
   'lambda '(point)
   (putnam-1970-b3-and-terms
    (list
     (list 'consp 'point)
     (putnam-1970-b3-static-apply-term
      carrier (list (list 'car 'point)))
     (putnam-1970-b3-static-apply-term
      carrier (list (list 'cdr 'point)))))))

(defun putnam-1970-b3-nth-term (index list-term)
  (list 'nth (putnam-1970-b3-quoted index) list-term))

(defun putnam-1970-b3-rectangle-subset-function
    (carrier less lower-x upper-x lower-y upper-y set)
  (list
   'lambda '(point)
   (putnam-1970-b3-implies-term
    (putnam-1970-b3-and-terms
     (list
      (list 'consp 'point)
      (putnam-1970-b3-static-apply-term
       carrier (list (list 'car 'point)))
      (putnam-1970-b3-static-apply-term
       carrier (list (list 'cdr 'point)))
      (putnam-1970-b3-static-apply-term
       less
       (list
        (putnam-1970-b3-quoted lower-x)
        (list 'car 'point)))
      (putnam-1970-b3-static-apply-term
       less
       (list
        (list 'car 'point)
        (putnam-1970-b3-quoted upper-x)))
      (putnam-1970-b3-static-apply-term
       less
       (list
        (putnam-1970-b3-quoted lower-y)
        (list 'cdr 'point)))
      (putnam-1970-b3-static-apply-term
       less
       (list
        (list 'cdr 'point)
        (putnam-1970-b3-quoted upper-y)))))
    (putnam-1970-b3-static-apply-term set '(point)))))

(defun putnam-1970-b3-rectangle-subset-p
    (carrier less lower-x upper-x lower-y upper-y set)
  (putnam-1970-b3-universal-p
   (putnam-1970-b3-rectangle-subset-function
    carrier less lower-x upper-x lower-y upper-y set)
   '(point)))

(defun putnam-1970-b3-plane-neighborhood-witness-function
    (carrier less set point)
  (let ((lower-x (putnam-1970-b3-nth-term 0 'bounds))
        (upper-x (putnam-1970-b3-nth-term 1 'bounds))
        (lower-y (putnam-1970-b3-nth-term 2 'bounds))
        (upper-y (putnam-1970-b3-nth-term 3 'bounds)))
    (list
     'lambda '(bounds)
     (putnam-1970-b3-and-terms
      (list
       (list 'true-listp 'bounds)
       (list 'equal
             (list 'len 'bounds)
             (putnam-1970-b3-quoted 4))
       (putnam-1970-b3-static-apply-term carrier (list lower-x))
       (putnam-1970-b3-static-apply-term carrier (list upper-x))
       (putnam-1970-b3-static-apply-term carrier (list lower-y))
       (putnam-1970-b3-static-apply-term carrier (list upper-y))
       (putnam-1970-b3-static-apply-term
        less
        (list
         lower-x
         (list 'car (putnam-1970-b3-quoted point))))
       (putnam-1970-b3-static-apply-term
        less
        (list
         (list 'car (putnam-1970-b3-quoted point))
         upper-x))
       (putnam-1970-b3-static-apply-term
        less
        (list
         lower-y
         (list 'cdr (putnam-1970-b3-quoted point))))
       (putnam-1970-b3-static-apply-term
        less
        (list
         (list 'cdr (putnam-1970-b3-quoted point))
         upper-y))
       (list
        'putnam-1970-b3-rectangle-subset-p
        (putnam-1970-b3-quoted carrier)
        (putnam-1970-b3-quoted less)
        lower-x upper-x lower-y upper-y
        (putnam-1970-b3-quoted set)))))))

(defun putnam-1970-b3-plane-neighborhood-p
    (carrier less set point)
  (putnam-1970-b3-exists-p
   (putnam-1970-b3-plane-neighborhood-witness-function
    carrier less set point)
   '(bounds)))

(defun putnam-1970-b3-plane-open-points-function
    (carrier less set)
  (let ((plane-carrier
         (putnam-1970-b3-plane-carrier carrier)))
    (list
     'lambda '(point)
     (putnam-1970-b3-implies-term
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-static-apply-term
         plane-carrier '(point))
        (putnam-1970-b3-static-apply-term set '(point))))
      (list
       'putnam-1970-b3-plane-neighborhood-p
       (putnam-1970-b3-quoted carrier)
       (putnam-1970-b3-quoted less)
       (putnam-1970-b3-quoted set)
       'point)))))

(defun putnam-1970-b3-plane-open-p
    (carrier less set)
  (let ((plane-carrier
         (putnam-1970-b3-plane-carrier carrier)))
    (and
     (putnam-1970-b3-valid-set-p plane-carrier set)
     (putnam-1970-b3-universal-p
      (putnam-1970-b3-plane-open-points-function
       carrier less set)
      '(point)))))

(defun putnam-1970-b3-plane-closed-p
    (carrier less set)
  (let ((plane-carrier
         (putnam-1970-b3-plane-carrier carrier)))
    (and
     (putnam-1970-b3-valid-set-p plane-carrier set)
     (putnam-1970-b3-plane-open-p
      carrier less
      (putnam-1970-b3-complement-set plane-carrier set)))))

;; The y-axis projection keeps the source's existential x-coordinate internal.

(defun putnam-1970-b3-projection-witness-function
    (carrier set y)
  (list
   'lambda '(x)
   (putnam-1970-b3-and-terms
    (list
     (putnam-1970-b3-static-apply-term carrier '(x))
     (putnam-1970-b3-static-apply-term
      set
      (list (list 'cons 'x (putnam-1970-b3-quoted y))))))))

(defun putnam-1970-b3-projection-member-p
    (carrier set y)
  (and
   (putnam-1970-b3-member-p carrier y)
   (putnam-1970-b3-exists-p
    (putnam-1970-b3-projection-witness-function
     carrier set y)
    '(x))))

(defun putnam-1970-b3-projection-set (carrier set)
  (list
   'lambda '(y)
   (putnam-1970-b3-and-terms
    (list
     (putnam-1970-b3-static-apply-term carrier '(y))
     (list
      'putnam-1970-b3-projection-member-p
      (putnam-1970-b3-quoted carrier)
      (putnam-1970-b3-quoted set)
      'y)))))

(defun putnam-1970-b3-strip-function
    (carrier less set a b)
  (let ((plane-carrier
         (putnam-1970-b3-plane-carrier carrier)))
    (list
     'lambda '(point)
     (putnam-1970-b3-implies-term
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-static-apply-term
         plane-carrier '(point))
        (putnam-1970-b3-static-apply-term set '(point))))
      (putnam-1970-b3-and-terms
       (list
        (putnam-1970-b3-static-apply-term
         less
         (list
          (putnam-1970-b3-quoted a)
          (list 'car 'point)))
        (putnam-1970-b3-static-apply-term
         less
         (list
          (list 'car 'point)
          (putnam-1970-b3-quoted b)))))))))

(defun putnam-1970-b3-strip-p
    (carrier less set a b)
  (putnam-1970-b3-universal-p
   (putnam-1970-b3-strip-function
    carrier less set a b)
   '(point)))

(defun putnambench-putnam-1970-b3-statement
    (ctx set a b)
  (let* ((carrier (putnam-1970-b3-r-carrier ctx))
         (less (putnam-1970-b3-r-less ctx))
         (plane-carrier
          (putnam-1970-b3-plane-carrier carrier)))
    (implies
     (and
      (putnam-1970-b3-context-p ctx)
      (putnam-1970-b3-member-p carrier a)
      (putnam-1970-b3-member-p carrier b)
      (putnam-1970-b3-binary-value less a b)
      (putnam-1970-b3-valid-set-p plane-carrier set)
      (putnam-1970-b3-strip-p carrier less set a b)
      (putnam-1970-b3-plane-closed-p carrier less set))
     (putnam-1970-b3-order-closed-p
      carrier less
      (putnam-1970-b3-projection-set carrier set)))))

(value-triple :itpeval-statement-checked)
:q
