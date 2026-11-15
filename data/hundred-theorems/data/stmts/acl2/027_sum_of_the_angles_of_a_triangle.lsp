;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__027, "Sum of the Angles of a Triangle": for any
;; three not-all-equal points in a real inner-product affine space, the three
;; principal interior angles, with a zero ray assigned pi/2, sum to pi. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context below presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. Three points in any real
;; inner-product affine space lie in an affine subspace of dimension at most
;; two, and their two displacement vectors have an isometric realization in
;; R^2. Thus universal quantification over the R^2 points below is
;; bidirectionally equivalent to universal quantification over the source
;; spaces for this three-point, angle-preserving statement.
;;
;; A principal angle is represented without transcendental primitives by a
;; homogeneous direction pair. For nonzero rays u and v the pair
;;
;;   (dot(u,v), |det(u,v)|)
;;
;; is the positive scalar multiple |u||v| * (cos(theta),sin(theta)), with
;; theta in [0,pi]. If either ray is zero, the pair is (0,1), exactly the
;; source convention theta = pi/2. Multiplication of these pairs is complex
;; multiplication. Since each of the three represented angles lies in
;; [0,pi], their product has zero imaginary part and negative real part
;; exactly when their sum is pi or 3*pi; the latter case occurs exactly when
;; all three angles are pi. Excluding that winding case therefore gives a
;; definitional, bidirectional encoding of equality of the angle sum with pi.

(defun ht027-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun ht027-unary-value (operation x)
  (apply$ operation (list x)))

(defun ht027-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk ht027-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (ht027-member-p carrier x))))

(defun-sk ht027-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (ht027-member-p carrier x)
          (ht027-member-p carrier y)
          (ht027-member-p carrier z))
     (and
      (ht027-member-p
       carrier (ht027-binary-value add x y))
      (ht027-member-p
       carrier (ht027-binary-value multiply x y))
      (ht027-member-p
       carrier (ht027-unary-value negate x))
      (implies
       (not (equal x zero))
       (ht027-member-p
        carrier (ht027-unary-value inverse x)))
      (equal
       (ht027-binary-value
        add (ht027-binary-value add x y) z)
       (ht027-binary-value
        add x (ht027-binary-value add y z)))
      (equal (ht027-binary-value add x y)
             (ht027-binary-value add y x))
      (equal (ht027-binary-value add x zero) x)
      (equal
       (ht027-binary-value
        add x (ht027-unary-value negate x))
       zero)
      (equal
       (ht027-binary-value
        multiply
        (ht027-binary-value multiply x y)
        z)
       (ht027-binary-value
        multiply
        x
        (ht027-binary-value multiply y z)))
      (equal (ht027-binary-value multiply x y)
             (ht027-binary-value multiply y x))
      (equal (ht027-binary-value multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (ht027-binary-value
         multiply x (ht027-unary-value inverse x))
        one))
      (equal
       (ht027-binary-value
        multiply x (ht027-binary-value add y z))
       (ht027-binary-value
        add
        (ht027-binary-value multiply x y)
        (ht027-binary-value multiply x z)))))))

(defun-sk ht027-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (ht027-member-p carrier x)
          (ht027-member-p carrier y)
          (ht027-member-p carrier z))
     (and
      (not (ht027-binary-value less x x))
      (or (equal x y)
          (ht027-binary-value less x y)
          (ht027-binary-value less y x))
      (implies
       (and (ht027-binary-value less x y)
            (ht027-binary-value less y z))
       (ht027-binary-value less x z))
      (implies
       (ht027-binary-value less x y)
       (ht027-binary-value
        less
        (ht027-binary-value add x z)
        (ht027-binary-value add y z)))
      (implies
       (and (ht027-binary-value less zero x)
            (ht027-binary-value less zero y))
       (ht027-binary-value
        less
        zero
        (ht027-binary-value multiply x y)))))))

(defun-sk ht027-set-nonempty-p (carrier set)
  (exists (x)
    (and (ht027-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk ht027-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and (ht027-member-p carrier x)
          (apply$ set (list x)))
     (not (ht027-binary-value less bound x)))))

(defun-sk ht027-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (ht027-member-p carrier bound)
     (ht027-upper-bound-p
      carrier less set bound))))

(defun-sk ht027-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (ht027-member-p carrier supremum)
     (ht027-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (ht027-member-p carrier bound)
       (ht027-upper-bound-p
        carrier less set bound))
      (not
       (ht027-binary-value
        less bound supremum))))))

(defun-sk ht027-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (ht027-supremum-p
     carrier less set supremum)))

(defun-sk ht027-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (ht027-valid-set-p carrier set)
      (ht027-set-nonempty-p carrier set)
      (ht027-bounded-above-p carrier less set))
     (ht027-has-supremum-p
      carrier less set))))

(defun ht027-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (ht027-member-p carrier zero)
   (ht027-member-p carrier one)
   (not (equal zero one))
   (ht027-field-laws-p
    carrier add multiply negate inverse zero one)
   (ht027-order-laws-p
    carrier add multiply zero less)
   (ht027-binary-value less zero one)
   (ht027-dedekind-complete-p carrier less)))

(defun ht027-r-carrier (ctx) (nth 0 ctx))
(defun ht027-r-zero (ctx) (nth 1 ctx))
(defun ht027-r-one (ctx) (nth 2 ctx))
(defun ht027-r-add (ctx) (nth 3 ctx))
(defun ht027-r-mul (ctx) (nth 4 ctx))
(defun ht027-r-neg (ctx) (nth 5 ctx))
(defun ht027-r-inv (ctx) (nth 6 ctx))
(defun ht027-r-lt (ctx) (nth 7 ctx))

(defun ht027-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (ht027-real-field-p
    (ht027-r-carrier ctx)
    (ht027-r-add ctx)
    (ht027-r-mul ctx)
    (ht027-r-neg ctx)
    (ht027-r-inv ctx)
    (ht027-r-zero ctx)
    (ht027-r-one ctx)
    (ht027-r-lt ctx))))

(defun ht027-r-add-value (ctx x y)
  (ht027-binary-value (ht027-r-add ctx) x y))

(defun ht027-r-mul-value (ctx x y)
  (ht027-binary-value (ht027-r-mul ctx) x y))

(defun ht027-r-neg-value (ctx x)
  (ht027-unary-value (ht027-r-neg ctx) x))

(defun ht027-r-sub-value (ctx x y)
  (ht027-r-add-value
   ctx x (ht027-r-neg-value ctx y)))

(defun ht027-r-lt-p (ctx x y)
  (if (ht027-binary-value
       (ht027-r-lt ctx) x y)
      t nil))

(defun ht027-r-abs-value (ctx x)
  (if (ht027-r-lt-p
       ctx x (ht027-r-zero ctx))
      (ht027-r-neg-value ctx x)
    x))

(defun ht027-point-p (ctx point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (ht027-member-p
    (ht027-r-carrier ctx) (nth 0 point))
   (ht027-member-p
    (ht027-r-carrier ctx) (nth 1 point))))

(defun ht027-vector-subtract (ctx left right)
  (list
   (ht027-r-sub-value
    ctx (nth 0 left) (nth 0 right))
   (ht027-r-sub-value
    ctx (nth 1 left) (nth 1 right))))

(defun ht027-vector-zero-p (ctx vector)
  (and
   (equal (nth 0 vector) (ht027-r-zero ctx))
   (equal (nth 1 vector) (ht027-r-zero ctx))))

(defun ht027-inner-product (ctx left right)
  (ht027-r-add-value
   ctx
   (ht027-r-mul-value
    ctx (nth 0 left) (nth 0 right))
   (ht027-r-mul-value
    ctx (nth 1 left) (nth 1 right))))

(defun ht027-determinant (ctx left right)
  (ht027-r-sub-value
   ctx
   (ht027-r-mul-value
    ctx (nth 0 left) (nth 1 right))
   (ht027-r-mul-value
    ctx (nth 1 left) (nth 0 right))))

(defun ht027-principal-angle-code
    (ctx first-point vertex third-point)
  (let ((first-ray
         (ht027-vector-subtract
          ctx first-point vertex))
        (second-ray
         (ht027-vector-subtract
          ctx third-point vertex)))
    (if (or (ht027-vector-zero-p ctx first-ray)
            (ht027-vector-zero-p ctx second-ray))
        (list (ht027-r-zero ctx)
              (ht027-r-one ctx))
      (list
       (ht027-inner-product
        ctx first-ray second-ray)
       (ht027-r-abs-value
        ctx
        (ht027-determinant
         ctx first-ray second-ray))))))

(defun ht027-angle-code-multiply (ctx left right)
  (list
   (ht027-r-sub-value
    ctx
    (ht027-r-mul-value
     ctx (nth 0 left) (nth 0 right))
    (ht027-r-mul-value
     ctx (nth 1 left) (nth 1 right)))
   (ht027-r-add-value
    ctx
    (ht027-r-mul-value
     ctx (nth 0 left) (nth 1 right))
    (ht027-r-mul-value
     ctx (nth 1 left) (nth 0 right)))))

(defun ht027-angle-code-pi-p (ctx code)
  (and
   (equal (nth 1 code) (ht027-r-zero ctx))
   (ht027-r-lt-p
    ctx (nth 0 code) (ht027-r-zero ctx))))

(defun ht027-three-principal-angles-sum-to-pi-p
    (ctx point-a point-b point-c)
  (let* ((angle-at-a
          (ht027-principal-angle-code
           ctx point-b point-a point-c))
         (angle-at-b
          (ht027-principal-angle-code
           ctx point-a point-b point-c))
         (angle-at-c
          (ht027-principal-angle-code
           ctx point-b point-c point-a))
         (product
          (ht027-angle-code-multiply
           ctx
           (ht027-angle-code-multiply
            ctx angle-at-a angle-at-b)
           angle-at-c)))
    (and
     (equal (nth 1 product) (ht027-r-zero ctx))
     (ht027-r-lt-p
      ctx (nth 0 product) (ht027-r-zero ctx))
     (not
      (and
       (ht027-angle-code-pi-p ctx angle-at-a)
       (ht027-angle-code-pi-p ctx angle-at-b)
       (ht027-angle-code-pi-p ctx angle-at-c))))))

(defun-sk
  hundred-theorems-027-sum-of-the-angles-of-a-triangle-statement
  (ctx)
  (forall (point-a point-b point-c)
    (implies
     (and
      (ht027-context-p ctx)
      (ht027-point-p ctx point-a)
      (ht027-point-p ctx point-b)
      (ht027-point-p ctx point-c)
      (not
       (and
        (equal point-a point-b)
        (equal point-b point-c)
        (equal point-a point-c))))
     (ht027-three-principal-angles-sum-to-pi-p
      ctx point-a point-b point-c))))

(value-triple :itpeval-statement-checked)
:q
