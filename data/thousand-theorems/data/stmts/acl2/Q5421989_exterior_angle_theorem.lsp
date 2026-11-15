;; Statement-only formalization of Thousand Theorems artifact Q5421989,
;; "Exterior angle theorem": when one side of a triangle is extended beyond
;; a vertex in a real inner-product affine space, the resulting exterior
;; angle equals the sum of the two remote interior angles. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The three collinear points in the strict-betweenness hypothesis together
;; with the remaining triangle vertex span an affine subspace of dimension at
;; most two. An affine isometry identifies that subspace with a subspace of
;; R^2, while every R^2 configuration is itself a source instance. Therefore
;; the coordinate statement below is bidirectionally equivalent to the
;; source's quantification over arbitrary real inner-product affine spaces.
;;
;; The scalar context presents a Dedekind-complete ordered field, hence the
;; real field up to ordered-field isomorphism; it does not restrict scalars to
;; ACL2's executable rationals.
;;
;; For two nonzero rays u and v, the pair
;;
;;   (dot(u,v), |det(u,v)|)
;;
;; is a positive multiple of (cos(theta), sin(theta)) for their principal
;; angle theta in [0,pi]. If either ray is zero, (0,1) represents Mathlib's
;; angle pi/2 convention. Complex multiplication adds represented angles.
;; Positive collinearity of the exterior-angle code with the product of the
;; two remote-angle codes therefore expresses exact angle addition; the
;; excluded (0, pi, pi) case removes the sole possible 2*pi wraparound.

(defun q5421989-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun q5421989-unary-value (operation x)
  (apply$ operation (list x)))

(defun q5421989-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk q5421989-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (q5421989-member-p carrier x))))

(defun-sk q5421989-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (q5421989-member-p carrier x)
          (q5421989-member-p carrier y)
          (q5421989-member-p carrier z))
     (and
      (q5421989-member-p
       carrier (q5421989-binary-value add x y))
      (q5421989-member-p
       carrier (q5421989-binary-value multiply x y))
      (q5421989-member-p
       carrier (q5421989-unary-value negate x))
      (implies
       (not (equal x zero))
       (q5421989-member-p
        carrier (q5421989-unary-value inverse x)))
      (equal
       (q5421989-binary-value
        add (q5421989-binary-value add x y) z)
       (q5421989-binary-value
        add x (q5421989-binary-value add y z)))
      (equal (q5421989-binary-value add x y)
             (q5421989-binary-value add y x))
      (equal (q5421989-binary-value add x zero) x)
      (equal
       (q5421989-binary-value
        add x (q5421989-unary-value negate x))
       zero)
      (equal
       (q5421989-binary-value
        multiply
        (q5421989-binary-value multiply x y)
        z)
       (q5421989-binary-value
        multiply
        x
        (q5421989-binary-value multiply y z)))
      (equal (q5421989-binary-value multiply x y)
             (q5421989-binary-value multiply y x))
      (equal (q5421989-binary-value multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (q5421989-binary-value
         multiply x (q5421989-unary-value inverse x))
        one))
      (equal
       (q5421989-binary-value
        multiply x (q5421989-binary-value add y z))
       (q5421989-binary-value
        add
        (q5421989-binary-value multiply x y)
        (q5421989-binary-value multiply x z)))))))

(defun-sk q5421989-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (q5421989-member-p carrier x)
          (q5421989-member-p carrier y)
          (q5421989-member-p carrier z))
     (and
      (not (q5421989-binary-value less x x))
      (or (equal x y)
          (q5421989-binary-value less x y)
          (q5421989-binary-value less y x))
      (implies
       (and (q5421989-binary-value less x y)
            (q5421989-binary-value less y z))
       (q5421989-binary-value less x z))
      (implies
       (q5421989-binary-value less x y)
       (q5421989-binary-value
        less
        (q5421989-binary-value add x z)
        (q5421989-binary-value add y z)))
      (implies
       (and (q5421989-binary-value less zero x)
            (q5421989-binary-value less zero y))
       (q5421989-binary-value
        less
        zero
        (q5421989-binary-value multiply x y)))))))

(defun-sk q5421989-set-nonempty-p (carrier set)
  (exists (x)
    (and (q5421989-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk q5421989-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and (q5421989-member-p carrier x)
          (apply$ set (list x)))
     (not (q5421989-binary-value less bound x)))))

(defun-sk q5421989-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q5421989-member-p carrier bound)
     (q5421989-upper-bound-p
      carrier less set bound))))

(defun-sk q5421989-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (q5421989-member-p carrier supremum)
     (q5421989-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (q5421989-member-p carrier bound)
       (q5421989-upper-bound-p
        carrier less set bound))
      (not
       (q5421989-binary-value
        less bound supremum))))))

(defun-sk q5421989-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (q5421989-supremum-p
     carrier less set supremum)))

(defun-sk q5421989-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (q5421989-valid-set-p carrier set)
      (q5421989-set-nonempty-p carrier set)
      (q5421989-bounded-above-p carrier less set))
     (q5421989-has-supremum-p
      carrier less set))))

(defun q5421989-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (q5421989-member-p carrier zero)
   (q5421989-member-p carrier one)
   (not (equal zero one))
   (q5421989-field-laws-p
    carrier add multiply negate inverse zero one)
   (q5421989-order-laws-p
    carrier add multiply zero less)
   (q5421989-binary-value less zero one)
   (q5421989-dedekind-complete-p carrier less)))

(defun q5421989-r-carrier (ctx) (nth 0 ctx))
(defun q5421989-r-zero (ctx) (nth 1 ctx))
(defun q5421989-r-one (ctx) (nth 2 ctx))
(defun q5421989-r-add (ctx) (nth 3 ctx))
(defun q5421989-r-mul (ctx) (nth 4 ctx))
(defun q5421989-r-neg (ctx) (nth 5 ctx))
(defun q5421989-r-inv (ctx) (nth 6 ctx))
(defun q5421989-r-lt (ctx) (nth 7 ctx))

(defun q5421989-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (q5421989-real-field-p
    (q5421989-r-carrier ctx)
    (q5421989-r-add ctx)
    (q5421989-r-mul ctx)
    (q5421989-r-neg ctx)
    (q5421989-r-inv ctx)
    (q5421989-r-zero ctx)
    (q5421989-r-one ctx)
    (q5421989-r-lt ctx))))

(defun q5421989-r-add-value (ctx x y)
  (q5421989-binary-value (q5421989-r-add ctx) x y))

(defun q5421989-r-mul-value (ctx x y)
  (q5421989-binary-value (q5421989-r-mul ctx) x y))

(defun q5421989-r-neg-value (ctx x)
  (q5421989-unary-value (q5421989-r-neg ctx) x))

(defun q5421989-r-sub-value (ctx x y)
  (q5421989-r-add-value
   ctx x (q5421989-r-neg-value ctx y)))

(defun q5421989-r-lt-p (ctx x y)
  (if (q5421989-binary-value
       (q5421989-r-lt ctx) x y)
      t nil))

(defun q5421989-r-abs-value (ctx x)
  (if (q5421989-r-lt-p
       ctx x (q5421989-r-zero ctx))
      (q5421989-r-neg-value ctx x)
    x))

(defun q5421989-point-p (ctx point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (q5421989-member-p
    (q5421989-r-carrier ctx) (nth 0 point))
   (q5421989-member-p
    (q5421989-r-carrier ctx) (nth 1 point))))

(defun q5421989-vector-subtract (ctx left right)
  (list
   (q5421989-r-sub-value
    ctx (nth 0 left) (nth 0 right))
   (q5421989-r-sub-value
    ctx (nth 1 left) (nth 1 right))))

(defun q5421989-vector-zero-p (ctx vector)
  (and
   (equal (nth 0 vector) (q5421989-r-zero ctx))
   (equal (nth 1 vector) (q5421989-r-zero ctx))))

(defun q5421989-inner-product (ctx left right)
  (q5421989-r-add-value
   ctx
   (q5421989-r-mul-value
    ctx (nth 0 left) (nth 0 right))
   (q5421989-r-mul-value
    ctx (nth 1 left) (nth 1 right))))

(defun q5421989-determinant (ctx left right)
  (q5421989-r-sub-value
   ctx
   (q5421989-r-mul-value
    ctx (nth 0 left) (nth 1 right))
   (q5421989-r-mul-value
    ctx (nth 1 left) (nth 0 right))))

(defun q5421989-line-map-coordinate
    (ctx left right parameter)
  (q5421989-r-add-value
   ctx
   left
   (q5421989-r-mul-value
    ctx parameter
    (q5421989-r-sub-value ctx right left))))

(defun-sk q5421989-strict-between-p
    (ctx left middle right)
  (exists (parameter)
    (and
     (q5421989-member-p
      (q5421989-r-carrier ctx) parameter)
     (q5421989-r-lt-p
      ctx (q5421989-r-zero ctx) parameter)
     (q5421989-r-lt-p
      ctx parameter (q5421989-r-one ctx))
     (not (equal middle left))
     (not (equal middle right))
     (equal
      (nth 0 middle)
      (q5421989-line-map-coordinate
       ctx (nth 0 left) (nth 0 right) parameter))
     (equal
      (nth 1 middle)
      (q5421989-line-map-coordinate
       ctx (nth 1 left) (nth 1 right) parameter)))))

(defun q5421989-principal-angle-code
    (ctx first-point vertex third-point)
  (let ((first-ray
         (q5421989-vector-subtract
          ctx first-point vertex))
        (second-ray
         (q5421989-vector-subtract
          ctx third-point vertex)))
    (if (or (q5421989-vector-zero-p ctx first-ray)
            (q5421989-vector-zero-p ctx second-ray))
        (list (q5421989-r-zero ctx)
              (q5421989-r-one ctx))
      (list
       (q5421989-inner-product
        ctx first-ray second-ray)
       (q5421989-r-abs-value
        ctx
        (q5421989-determinant
         ctx first-ray second-ray))))))

(defun q5421989-angle-code-multiply (ctx left right)
  (list
   (q5421989-r-sub-value
    ctx
    (q5421989-r-mul-value
     ctx (nth 0 left) (nth 0 right))
    (q5421989-r-mul-value
     ctx (nth 1 left) (nth 1 right)))
   (q5421989-r-add-value
    ctx
    (q5421989-r-mul-value
     ctx (nth 0 left) (nth 1 right))
    (q5421989-r-mul-value
     ctx (nth 1 left) (nth 0 right)))))

(defun q5421989-angle-code-zero-p (ctx code)
  (and
   (equal (nth 1 code) (q5421989-r-zero ctx))
   (q5421989-r-lt-p
    ctx (q5421989-r-zero ctx) (nth 0 code))))

(defun q5421989-angle-code-pi-p (ctx code)
  (and
   (equal (nth 1 code) (q5421989-r-zero ctx))
   (q5421989-r-lt-p
    ctx (nth 0 code) (q5421989-r-zero ctx))))

(defun q5421989-angle-equals-sum-p
    (ctx exterior first-remote second-remote)
  (let ((remote-sum
         (q5421989-angle-code-multiply
          ctx first-remote second-remote)))
    (and
     (equal
      (q5421989-determinant ctx exterior remote-sum)
      (q5421989-r-zero ctx))
     (q5421989-r-lt-p
      ctx
      (q5421989-r-zero ctx)
      (q5421989-inner-product ctx exterior remote-sum))
     (not
      (and
       (q5421989-angle-code-zero-p ctx exterior)
       (q5421989-angle-code-pi-p ctx first-remote)
       (q5421989-angle-code-pi-p ctx second-remote))))))

(defun q5421989-exterior-angle-conclusion-p
    (ctx p1 p2 p3 p)
  (q5421989-angle-equals-sum-p
   ctx
   (q5421989-principal-angle-code ctx p3 p1 p)
   (q5421989-principal-angle-code ctx p1 p3 p2)
   (q5421989-principal-angle-code ctx p3 p2 p1)))

(defun-sk thousand-theorems-q5421989-exterior-angle-statement
    (ctx)
  (forall (p1 p2 p3 p)
    (implies
     (and
      (q5421989-context-p ctx)
      (q5421989-point-p ctx p1)
      (q5421989-point-p ctx p2)
      (q5421989-point-p ctx p3)
      (q5421989-point-p ctx p)
      (q5421989-strict-between-p ctx p p1 p2))
     (q5421989-exterior-angle-conclusion-p
      ctx p1 p2 p3 p))))

(value-triple :itpeval-statement-checked)
:q
