;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_a5:
;; area-definiteness of real coefficients for every planar point configuration
;; implies area-definiteness for every spatial configuration. This file contains no proof.

(in-package "ACL2")

;; The real scalar domain is presented as an arbitrary real closed ordered
;; field.  Real closed fields have the same first-order theory as the reals,
;; and all formulas below use only ordered-field operations and the unique
;; nonnegative square root.  Thus this presentation is bidirectionally
;; equivalent to the source statement over R.
;;
;; A function Fin m x Fin m x Fin m -> R is represented exactly by a list of
;; length m^3, and a configuration Fin m -> R^d by a list of m d-tuples.
;; DEFUN-SK directly quantifies over every such configuration.  The
;; triangle-area terms are sqrt(det^2)/2 in dimension two and
;; sqrt(||u cross v||^2)/2 in dimension three, the standard algebraic
;; formulas for the source Euclidean areas.

(defun putnam-2013-a5-quoted (object)
  (list 'quote object))

(defun putnam-2013-a5-apply1-term (function argument)
  (list
   'apply$
   (putnam-2013-a5-quoted function)
   (list 'cons argument nil)))

(defun putnam-2013-a5-apply2-term (function left right)
  (list
   'apply$
   (putnam-2013-a5-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2013-a5-and-term (terms)
  (if (endp terms)
      (putnam-2013-a5-quoted t)
    (list
     'if
     (car terms)
     (putnam-2013-a5-and-term (cdr terms))
     (putnam-2013-a5-quoted nil))))

(defun putnam-2013-a5-or-term (terms)
  (if (endp terms)
      (putnam-2013-a5-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2013-a5-quoted t)
     (putnam-2013-a5-or-term (cdr terms)))))

(defun putnam-2013-a5-not-term (term)
  (list
   'if
   term
   (putnam-2013-a5-quoted nil)
   (putnam-2013-a5-quoted t)))

(defun putnam-2013-a5-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2013-a5-quoted t)))

(defun putnam-2013-a5-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2013-a5-quoted t)))

(defun putnam-2013-a5-carrier-term (carrier element)
  (putnam-2013-a5-apply1-term carrier element))

(defun putnam-2013-a5-operation-term (operation left right)
  (putnam-2013-a5-apply2-term operation left right))

(defun putnam-2013-a5-all-coefficients-function ()
  '(lambda (loop$-gvars loop$-ivars)
     (apply$ (car loop$-gvars)
             (cons loop$-ivars 'nil))))

(defun putnam-2013-a5-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2013-a5-quoted
    (putnam-2013-a5-all-coefficients-function))
   (list 'cons
         (putnam-2013-a5-quoted carrier)
         nil)
   coefficients))

(defun putnam-2013-a5-polynomial-term
    (carrier zero coefficients)
  (putnam-2013-a5-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2013-a5-all-coefficients-term
     carrier coefficients)
    (putnam-2013-a5-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2013-a5-quoted 1))
      (putnam-2013-a5-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2013-a5-quoted zero))))))))

(defun putnam-2013-a5-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2013-a5-quoted zero))
         (qone (putnam-2013-a5-quoted one))
         (add-xy
          (putnam-2013-a5-operation-term add x y))
         (add-yz
          (putnam-2013-a5-operation-term add y z))
         (mul-xy
          (putnam-2013-a5-operation-term mul x y))
         (mul-yz
          (putnam-2013-a5-operation-term mul y z))
         (neg-x
          (putnam-2013-a5-apply1-term neg x))
         (inv-x
          (putnam-2013-a5-apply1-term inv x))
         (domain
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term carrier x)
            (putnam-2013-a5-carrier-term carrier y)
            (putnam-2013-a5-carrier-term carrier z))))
         (laws
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term carrier add-xy)
            (putnam-2013-a5-carrier-term carrier mul-xy)
            (putnam-2013-a5-carrier-term carrier neg-x)
            (putnam-2013-a5-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2013-a5-operation-term add add-xy z)
             (putnam-2013-a5-operation-term add x add-yz))
            (list
             'equal
             (putnam-2013-a5-operation-term mul mul-xy z)
             (putnam-2013-a5-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2013-a5-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2013-a5-operation-term mul y x))
            (list
             'equal
             (putnam-2013-a5-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2013-a5-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2013-a5-operation-term mul x qone)
             x)
            (putnam-2013-a5-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2013-a5-implies-term
             (putnam-2013-a5-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2013-a5-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2013-a5-operation-term mul x add-yz)
             (putnam-2013-a5-operation-term
              add
              (putnam-2013-a5-operation-term mul x y)
              (putnam-2013-a5-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2013-a5-implies-term domain laws))))

(defun putnam-2013-a5-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2013-a5-quoted zero))
         (lt-xy
          (putnam-2013-a5-operation-term lt x y))
         (lt-yx
          (putnam-2013-a5-operation-term lt y x))
         (lt-yz
          (putnam-2013-a5-operation-term lt y z))
         (lt-xz
          (putnam-2013-a5-operation-term lt x z))
         (domain
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term carrier x)
            (putnam-2013-a5-carrier-term carrier y)
            (putnam-2013-a5-carrier-term carrier z))))
         (laws
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-not-term
             (putnam-2013-a5-operation-term lt x x))
            (putnam-2013-a5-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2013-a5-implies-term
             (putnam-2013-a5-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2013-a5-implies-term
             lt-xy
             (putnam-2013-a5-operation-term
              lt
              (putnam-2013-a5-operation-term add x z)
              (putnam-2013-a5-operation-term add y z)))
            (putnam-2013-a5-implies-term
             (putnam-2013-a5-and-term
              (list
               (putnam-2013-a5-operation-term lt qzero x)
               (putnam-2013-a5-operation-term lt qzero y)))
             (putnam-2013-a5-operation-term
              lt
              qzero
              (putnam-2013-a5-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2013-a5-implies-term domain laws))))

(defun putnam-2013-a5-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2013-a5-quoted zero))
         (root
          (putnam-2013-a5-apply1-term square-root x))
         (domain
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term carrier x)
            (putnam-2013-a5-not-term
             (putnam-2013-a5-operation-term lt x qzero)))))
         (laws
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term carrier root)
            (putnam-2013-a5-not-term
             (putnam-2013-a5-operation-term lt root qzero))
            (list
             'equal
             (putnam-2013-a5-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2013-a5-implies-term domain laws))))

(defun putnam-2013-a5-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2013-a5-quoted zero))
         (domain
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2013-a5-all-coefficients-term
             carrier rest)
            (putnam-2013-a5-carrier-term carrier x))))
         (empty-law
          (putnam-2013-a5-implies-term
           (putnam-2013-a5-carrier-term carrier x)
           (list
            'equal
            (putnam-2013-a5-operation-term
             evaluate
             (putnam-2013-a5-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2013-a5-operation-term
           add
           coefficient
           (putnam-2013-a5-operation-term
            mul
            x
            (putnam-2013-a5-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2013-a5-implies-term
           domain
           (putnam-2013-a5-and-term
            (list
             (putnam-2013-a5-carrier-term
              carrier
              (putnam-2013-a5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2013-a5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2013-a5-and-term
      (list empty-law recursive-law)))))

(defun putnam-2013-a5-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2013-a5-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2013-a5-and-term
           (list
            (putnam-2013-a5-carrier-term carrier root)
            (list
             'equal
             (putnam-2013-a5-operation-term
              evaluate coefficients root)
             (putnam-2013-a5-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2013-a5-implies-term domain laws))))

(defun putnam-2013-a5-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root evaluate)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (tamep-functionp evaluate)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (fn-equal
    (putnam-2013-a5-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-2013-a5-true-function '(x y z)))
   (fn-equal
    (putnam-2013-a5-order-laws-function
     carrier zero add mul lt)
    (putnam-2013-a5-true-function '(x y z)))
   (fn-equal
    (putnam-2013-a5-square-root-laws-function
     carrier zero mul lt square-root)
    (putnam-2013-a5-true-function '(x)))
   (fn-equal
    (putnam-2013-a5-evaluation-laws-function
     carrier zero add mul evaluate)
    (putnam-2013-a5-true-function
     '(coefficient rest x)))
   (fn-equal
    (putnam-2013-a5-odd-root-laws-function
     carrier zero evaluate odd-root)
    (putnam-2013-a5-true-function
     '(coefficients)))))

(defun putnam-2013-a5-carrier-list-p (values carrier)
  (if (endp values)
      (equal values nil)
    (and
     (apply$ carrier (list (car values)))
     (putnam-2013-a5-carrier-list-p
      (cdr values) carrier))))

(defun putnam-2013-a5-coefficient-table-p
    (m coefficients carrier)
  (and
   (natp m)
   (true-listp coefficients)
   (equal (len coefficients)
          (* m m m))
   (putnam-2013-a5-carrier-list-p
    coefficients carrier)))

(defun putnam-2013-a5-nth-term (index sequence)
  (list
   'nth
   (putnam-2013-a5-quoted index)
   sequence))

(defun putnam-2013-a5-point-term
    (point dimension carrier coordinate)
  (declare (xargs :measure (nfix coordinate)))
  (if (zp coordinate)
      (putnam-2013-a5-and-term
       (list
        (list 'true-listp point)
        (list
         'equal
         (list 'len point)
         (putnam-2013-a5-quoted dimension))))
    (putnam-2013-a5-and-term
     (list
      (putnam-2013-a5-carrier-term
       carrier
       (putnam-2013-a5-nth-term
        (- coordinate 1) point))
      (putnam-2013-a5-point-term
       point dimension carrier (- coordinate 1))))))

(defun putnam-2013-a5-configuration-term
    (m dimension carrier count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-2013-a5-and-term
       (list
        (list 'true-listp 'configuration)
        (list
         'equal
         (list 'len 'configuration)
         (putnam-2013-a5-quoted m))))
    (putnam-2013-a5-and-term
     (list
      (putnam-2013-a5-point-term
       (putnam-2013-a5-nth-term
        (- count 1) 'configuration)
       dimension
       carrier
       dimension)
      (putnam-2013-a5-configuration-term
       m dimension carrier (- count 1))))))

(defun putnam-2013-a5-add-term (add left right)
  (putnam-2013-a5-operation-term add left right))

(defun putnam-2013-a5-mul-term (mul left right)
  (putnam-2013-a5-operation-term mul left right))

(defun putnam-2013-a5-neg-term (neg value)
  (putnam-2013-a5-apply1-term neg value))

(defun putnam-2013-a5-sub-term (add neg left right)
  (putnam-2013-a5-add-term
   add left
   (putnam-2013-a5-neg-term neg right)))

(defun putnam-2013-a5-coordinate-term
    (point-index coordinate-index)
  (putnam-2013-a5-nth-term
   coordinate-index
   (putnam-2013-a5-nth-term
    point-index 'configuration)))

(defun putnam-2013-a5-area2-term
    (i j k one add mul neg inv square-root)
  (let* ((ax (putnam-2013-a5-coordinate-term i 0))
         (ay (putnam-2013-a5-coordinate-term i 1))
         (bx (putnam-2013-a5-coordinate-term j 0))
         (by (putnam-2013-a5-coordinate-term j 1))
         (cx (putnam-2013-a5-coordinate-term k 0))
         (cy (putnam-2013-a5-coordinate-term k 1))
         (ux (putnam-2013-a5-sub-term add neg bx ax))
         (uy (putnam-2013-a5-sub-term add neg by ay))
         (vx (putnam-2013-a5-sub-term add neg cx ax))
         (vy (putnam-2013-a5-sub-term add neg cy ay))
         (det
          (putnam-2013-a5-sub-term
           add neg
           (putnam-2013-a5-mul-term mul ux vy)
           (putnam-2013-a5-mul-term mul uy vx)))
         (two
          (putnam-2013-a5-add-term
           add
           (putnam-2013-a5-quoted one)
           (putnam-2013-a5-quoted one))))
    (putnam-2013-a5-mul-term
     mul
     (putnam-2013-a5-apply1-term
      square-root
      (putnam-2013-a5-mul-term mul det det))
     (putnam-2013-a5-apply1-term inv two))))

(defun putnam-2013-a5-area3-term
    (i j k one add mul neg inv square-root)
  (let* ((ax (putnam-2013-a5-coordinate-term i 0))
         (ay (putnam-2013-a5-coordinate-term i 1))
         (az (putnam-2013-a5-coordinate-term i 2))
         (bx (putnam-2013-a5-coordinate-term j 0))
         (by (putnam-2013-a5-coordinate-term j 1))
         (bz (putnam-2013-a5-coordinate-term j 2))
         (cx (putnam-2013-a5-coordinate-term k 0))
         (cy (putnam-2013-a5-coordinate-term k 1))
         (cz (putnam-2013-a5-coordinate-term k 2))
         (ux (putnam-2013-a5-sub-term add neg bx ax))
         (uy (putnam-2013-a5-sub-term add neg by ay))
         (uz (putnam-2013-a5-sub-term add neg bz az))
         (vx (putnam-2013-a5-sub-term add neg cx ax))
         (vy (putnam-2013-a5-sub-term add neg cy ay))
         (vz (putnam-2013-a5-sub-term add neg cz az))
         (cross-x
          (putnam-2013-a5-sub-term
           add neg
           (putnam-2013-a5-mul-term mul uy vz)
           (putnam-2013-a5-mul-term mul uz vy)))
         (cross-y
          (putnam-2013-a5-sub-term
           add neg
           (putnam-2013-a5-mul-term mul uz vx)
           (putnam-2013-a5-mul-term mul ux vz)))
         (cross-z
          (putnam-2013-a5-sub-term
           add neg
           (putnam-2013-a5-mul-term mul ux vy)
           (putnam-2013-a5-mul-term mul uy vx)))
         (norm-square
          (putnam-2013-a5-add-term
           add
           (putnam-2013-a5-mul-term
            mul cross-x cross-x)
           (putnam-2013-a5-add-term
            add
            (putnam-2013-a5-mul-term
             mul cross-y cross-y)
            (putnam-2013-a5-mul-term
             mul cross-z cross-z))))
         (two
          (putnam-2013-a5-add-term
           add
           (putnam-2013-a5-quoted one)
           (putnam-2013-a5-quoted one))))
    (putnam-2013-a5-mul-term
     mul
     (putnam-2013-a5-apply1-term
      square-root norm-square)
     (putnam-2013-a5-apply1-term inv two))))

(defun putnam-2013-a5-coefficient-index (m i j k)
  (+ (* i m m)
     (* j m)
     k))

(defun putnam-2013-a5-weighted-term
    (dimension m coefficients i j k
               one add mul neg inv square-root)
  (let ((coefficient
         (putnam-2013-a5-nth-term
          (putnam-2013-a5-coefficient-index m i j k)
          (putnam-2013-a5-quoted coefficients))))
    (putnam-2013-a5-mul-term
     mul
     coefficient
     (if (equal dimension 2)
         (putnam-2013-a5-area2-term
          i j k one add mul neg inv square-root)
       (putnam-2013-a5-area3-term
        i j k one add mul neg inv square-root)))))

(defun putnam-2013-a5-sum-k-term
    (dimension m coefficients i j count
               zero one add mul neg inv square-root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-2013-a5-quoted zero)
    (let ((k (- count 1)))
      (if (and (< i j)
               (< j k))
          (putnam-2013-a5-add-term
           add
           (putnam-2013-a5-weighted-term
            dimension m coefficients i j k
            one add mul neg inv square-root)
           (putnam-2013-a5-sum-k-term
            dimension m coefficients i j k
            zero one add mul neg inv square-root))
        (putnam-2013-a5-sum-k-term
         dimension m coefficients i j k
         zero one add mul neg inv square-root)))))

(defun putnam-2013-a5-sum-j-term
    (dimension m coefficients i count
               zero one add mul neg inv square-root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-2013-a5-quoted zero)
    (let ((j (- count 1)))
      (putnam-2013-a5-add-term
       add
       (putnam-2013-a5-sum-k-term
        dimension m coefficients i j m
        zero one add mul neg inv square-root)
       (putnam-2013-a5-sum-j-term
        dimension m coefficients i j
        zero one add mul neg inv square-root)))))

(defun putnam-2013-a5-sum-i-term
    (dimension m coefficients count
               zero one add mul neg inv square-root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-2013-a5-quoted zero)
    (let ((i (- count 1)))
      (putnam-2013-a5-add-term
       add
       (putnam-2013-a5-sum-j-term
        dimension m coefficients i m
        zero one add mul neg inv square-root)
       (putnam-2013-a5-sum-i-term
        dimension m coefficients i
        zero one add mul neg inv square-root)))))

(defun putnam-2013-a5-apply1
    (function argument)
  (apply$ function (list argument)))

(defun putnam-2013-a5-apply2
    (function left right)
  (apply$ function (list left right)))

(defun putnam-2013-a5-point-p
    (point dimension carrier)
  (and
   (true-listp point)
   (equal (len point) dimension)
   (putnam-2013-a5-carrier-list-p point carrier)))

(defun putnam-2013-a5-point-list-p
    (points dimension carrier)
  (if (endp points)
      (equal points nil)
    (and
     (putnam-2013-a5-point-p
      (car points) dimension carrier)
     (putnam-2013-a5-point-list-p
      (cdr points) dimension carrier))))

(defun putnam-2013-a5-configuration-p
    (configuration m dimension carrier)
  (and
   (true-listp configuration)
   (equal (len configuration) m)
   (putnam-2013-a5-point-list-p
    configuration dimension carrier)))

(defun putnam-2013-a5-sub
    (add neg left right)
  (putnam-2013-a5-apply2
   add left
   (putnam-2013-a5-apply1 neg right)))

(defun putnam-2013-a5-coordinate
    (configuration point-index coordinate-index)
  (nth coordinate-index
       (nth point-index configuration)))

(defun putnam-2013-a5-area2
    (configuration i j k one add mul neg inv square-root)
  (let* ((ax (putnam-2013-a5-coordinate configuration i 0))
         (ay (putnam-2013-a5-coordinate configuration i 1))
         (bx (putnam-2013-a5-coordinate configuration j 0))
         (by (putnam-2013-a5-coordinate configuration j 1))
         (cx (putnam-2013-a5-coordinate configuration k 0))
         (cy (putnam-2013-a5-coordinate configuration k 1))
         (ux (putnam-2013-a5-sub add neg bx ax))
         (uy (putnam-2013-a5-sub add neg by ay))
         (vx (putnam-2013-a5-sub add neg cx ax))
         (vy (putnam-2013-a5-sub add neg cy ay))
         (det
          (putnam-2013-a5-sub
           add neg
           (putnam-2013-a5-apply2 mul ux vy)
           (putnam-2013-a5-apply2 mul uy vx)))
         (two (putnam-2013-a5-apply2 add one one)))
    (putnam-2013-a5-apply2
     mul
     (putnam-2013-a5-apply1
      square-root
      (putnam-2013-a5-apply2 mul det det))
     (putnam-2013-a5-apply1 inv two))))

(defun putnam-2013-a5-area3
    (configuration i j k one add mul neg inv square-root)
  (let* ((ax (putnam-2013-a5-coordinate configuration i 0))
         (ay (putnam-2013-a5-coordinate configuration i 1))
         (az (putnam-2013-a5-coordinate configuration i 2))
         (bx (putnam-2013-a5-coordinate configuration j 0))
         (by (putnam-2013-a5-coordinate configuration j 1))
         (bz (putnam-2013-a5-coordinate configuration j 2))
         (cx (putnam-2013-a5-coordinate configuration k 0))
         (cy (putnam-2013-a5-coordinate configuration k 1))
         (cz (putnam-2013-a5-coordinate configuration k 2))
         (ux (putnam-2013-a5-sub add neg bx ax))
         (uy (putnam-2013-a5-sub add neg by ay))
         (uz (putnam-2013-a5-sub add neg bz az))
         (vx (putnam-2013-a5-sub add neg cx ax))
         (vy (putnam-2013-a5-sub add neg cy ay))
         (vz (putnam-2013-a5-sub add neg cz az))
         (cross-x
          (putnam-2013-a5-sub
           add neg
           (putnam-2013-a5-apply2 mul uy vz)
           (putnam-2013-a5-apply2 mul uz vy)))
         (cross-y
          (putnam-2013-a5-sub
           add neg
           (putnam-2013-a5-apply2 mul uz vx)
           (putnam-2013-a5-apply2 mul ux vz)))
         (cross-z
          (putnam-2013-a5-sub
           add neg
           (putnam-2013-a5-apply2 mul ux vy)
           (putnam-2013-a5-apply2 mul uy vx)))
         (norm-square
          (putnam-2013-a5-apply2
           add
           (putnam-2013-a5-apply2 mul cross-x cross-x)
           (putnam-2013-a5-apply2
            add
            (putnam-2013-a5-apply2 mul cross-y cross-y)
            (putnam-2013-a5-apply2 mul cross-z cross-z))))
         (two (putnam-2013-a5-apply2 add one one)))
    (putnam-2013-a5-apply2
     mul
     (putnam-2013-a5-apply1 square-root norm-square)
     (putnam-2013-a5-apply1 inv two))))

(defun putnam-2013-a5-weighted-value
    (dimension m coefficients configuration i j k
               one add mul neg inv square-root)
  (putnam-2013-a5-apply2
   mul
   (nth (putnam-2013-a5-coefficient-index m i j k)
        coefficients)
   (if (equal dimension 2)
       (putnam-2013-a5-area2
        configuration i j k
        one add mul neg inv square-root)
     (putnam-2013-a5-area3
      configuration i j k
      one add mul neg inv square-root))))

(defun putnam-2013-a5-sum-k
    (dimension m coefficients configuration i j count
               zero one add mul neg inv square-root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((k (- (nfix count) 1)))
      (if (and (< i j) (< j k))
          (putnam-2013-a5-apply2
           add
           (putnam-2013-a5-weighted-value
            dimension m coefficients configuration i j k
            one add mul neg inv square-root)
           (putnam-2013-a5-sum-k
            dimension m coefficients configuration i j k
            zero one add mul neg inv square-root))
        (putnam-2013-a5-sum-k
         dimension m coefficients configuration i j k
         zero one add mul neg inv square-root)))))

(defun putnam-2013-a5-sum-j
    (dimension m coefficients configuration i count
               zero one add mul neg inv square-root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((j (- (nfix count) 1)))
      (putnam-2013-a5-apply2
       add
       (putnam-2013-a5-sum-k
        dimension m coefficients configuration i j m
        zero one add mul neg inv square-root)
       (putnam-2013-a5-sum-j
        dimension m coefficients configuration i j
        zero one add mul neg inv square-root)))))

(defun putnam-2013-a5-sum-i
    (dimension m coefficients configuration count
               zero one add mul neg inv square-root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((i (- (nfix count) 1)))
      (putnam-2013-a5-apply2
       add
       (putnam-2013-a5-sum-j
        dimension m coefficients configuration i m
        zero one add mul neg inv square-root)
       (putnam-2013-a5-sum-i
        dimension m coefficients configuration i
        zero one add mul neg inv square-root)))))

(defun-sk putnam-2013-a5-area-definite-p
    (dimension m coefficients carrier zero one
               add mul neg inv lt square-root)
  (forall (configuration)
    (implies
     (putnam-2013-a5-configuration-p
      configuration m dimension carrier)
     (not
      (putnam-2013-a5-apply2
       lt
       (putnam-2013-a5-sum-i
        dimension m coefficients configuration m
        zero one add mul neg inv square-root)
       zero)))))

(defun putnambench-putnam-2013-a5-statement
    (m coefficients
       carrier zero one add mul neg inv lt square-root odd-root evaluate)
  (implies
   (and
    (natp m)
    (<= 3 m)
    (putnam-2013-a5-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root evaluate)
    (putnam-2013-a5-coefficient-table-p
     m coefficients carrier))
   (implies
    (putnam-2013-a5-area-definite-p
     2 m coefficients carrier zero one
     add mul neg inv lt square-root)
    (putnam-2013-a5-area-definite-p
     3 m coefficients carrier zero one
     add mul neg inv lt square-root))))

(value-triple :itpeval-statement-checked)
:q
