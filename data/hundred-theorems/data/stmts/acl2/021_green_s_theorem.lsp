;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__021, "Green's Theorem": a C1 planar vector field
;; has circulation around a closed absolutely continuous path equal to the
;; integral of its scalar curl over the winding-number-one interior. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the real numbers as a Dedekind-complete
;; ordered field. Paths, fields, sets, and gauges are arbitrary tame APPLY$
;; functions, not finite tables.

(defun ht021-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun ht021-unary (function x)
  (apply$ function (list x)))

(defun ht021-binary (function x y)
  (apply$ function (list x y)))

(defun-sk ht021-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (ht021-member-p carrier x)
          (ht021-member-p carrier y)
          (ht021-member-p carrier z))
     (and
      (ht021-member-p carrier (ht021-binary add x y))
      (ht021-member-p carrier (ht021-binary multiply x y))
      (ht021-member-p carrier (ht021-unary negate x))
      (ht021-member-p carrier (ht021-unary inverse x))
      (equal (ht021-binary add (ht021-binary add x y) z)
             (ht021-binary add x (ht021-binary add y z)))
      (equal (ht021-binary add x y) (ht021-binary add y x))
      (equal (ht021-binary add x zero) x)
      (equal (ht021-binary add x (ht021-unary negate x)) zero)
      (equal
       (ht021-binary multiply (ht021-binary multiply x y) z)
       (ht021-binary multiply x (ht021-binary multiply y z)))
      (equal (ht021-binary multiply x y)
             (ht021-binary multiply y x))
      (equal (ht021-binary multiply x one) x)
      (implies (equal x zero)
               (equal (ht021-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal (ht021-binary multiply x (ht021-unary inverse x)) one))
      (equal
       (ht021-binary multiply x (ht021-binary add y z))
       (ht021-binary
        add
        (ht021-binary multiply x y)
        (ht021-binary multiply x z)))))))

(defun-sk ht021-order-laws-p (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (ht021-member-p carrier x)
          (ht021-member-p carrier y)
          (ht021-member-p carrier z))
     (and
      (not (ht021-binary less x x))
      (or (equal x y)
          (ht021-binary less x y)
          (ht021-binary less y x))
      (implies
       (and (ht021-binary less x y)
            (ht021-binary less y z))
       (ht021-binary less x z))
      (implies
       (ht021-binary less x y)
       (ht021-binary
        less (ht021-binary add x z) (ht021-binary add y z)))
      (implies
       (and (ht021-binary less zero x)
            (ht021-binary less zero y))
       (ht021-binary less zero (ht021-binary multiply x y)))))))

(defun-sk ht021-set-nonempty-p (carrier set)
  (exists (x)
    (and (ht021-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk ht021-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (ht021-member-p carrier x)
          (apply$ set (list x)))
     (not (ht021-binary less bound x)))))

(defun-sk ht021-bounded-above-p (carrier less set)
  (exists (bound)
    (and (ht021-member-p carrier bound)
         (ht021-upper-bound-p carrier less set bound))))

(defun-sk ht021-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (ht021-member-p carrier supremum)
     (ht021-upper-bound-p carrier less set supremum)
     (implies
      (and (ht021-member-p carrier bound)
           (ht021-upper-bound-p carrier less set bound))
      (not (ht021-binary less bound supremum))))))

(defun-sk ht021-has-supremum-p (carrier less set)
  (exists (supremum)
    (ht021-supremum-p carrier less set supremum)))

(defun-sk ht021-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (ht021-set-nonempty-p carrier set)
          (ht021-bounded-above-p carrier less set))
     (ht021-has-supremum-p carrier less set))))

(defun ht021-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (ht021-member-p carrier zero)
   (ht021-member-p carrier one)
   (not (equal zero one))
   (ht021-field-laws-p
    carrier add multiply negate inverse zero one)
   (ht021-order-laws-p carrier add multiply zero less)
   (ht021-binary less zero one)
   (ht021-dedekind-complete-p carrier less)))

(defun ht021-add (add x y)
  (ht021-binary add x y))

(defun ht021-neg (negate x)
  (ht021-unary negate x))

(defun ht021-sub (add negate x y)
  (ht021-add add x (ht021-neg negate y)))

(defun ht021-mul (multiply x y)
  (ht021-binary multiply x y))

(defun ht021-inv (inverse x)
  (ht021-unary inverse x))

(defun ht021-less-p (less x y)
  (if (ht021-binary less x y) t nil))

(defun ht021-leq-p (less x y)
  (not (ht021-less-p less y x)))

(defun ht021-abs (less negate zero x)
  (if (ht021-less-p less x zero)
      (ht021-neg negate x)
    x))

(defun ht021-max (less x y)
  (if (ht021-less-p less x y) y x))

(defun ht021-positive-p (carrier less zero x)
  (and (ht021-member-p carrier x)
       (ht021-less-p less zero x)))

(defun ht021-two (add one)
  (ht021-add add one one))

(defun ht021-four (add one)
  (ht021-two add (ht021-two add one)))

(defun ht021-square (multiply x)
  (ht021-mul multiply x x))

(defun ht021-plane-distance
    (add negate less zero x1 y1 x2 y2)
  (ht021-max
   less
   (ht021-abs less negate zero (ht021-sub add negate x1 x2))
   (ht021-abs less negate zero (ht021-sub add negate y1 y2))))

(defun-sk ht021-unary-real-function-p (carrier function)
  (forall (x)
    (implies
     (ht021-member-p carrier x)
     (ht021-member-p carrier (ht021-unary function x)))))

(defun-sk ht021-binary-real-function-p (carrier function)
  (forall (x y)
    (implies
     (and (ht021-member-p carrier x)
          (ht021-member-p carrier y))
     (ht021-member-p carrier (ht021-binary function x y)))))

(defun ht021-valid-unary-function-p (carrier function)
  (and (tamep-functionp function)
       (ht021-unary-real-function-p carrier function)))

(defun ht021-valid-binary-function-p (carrier function)
  (and (tamep-functionp function)
       (ht021-binary-real-function-p carrier function)))

(defun ht021-in-interval-p (less a b x)
  (and (ht021-leq-p less a x)
       (ht021-leq-p less x b)))

;; Absolute continuity is the standard finite disjoint-interval definition.

(defun ht021-interval-family-p (carrier less zero one intervals previous)
  (if (consp intervals)
      (let* ((entry (car intervals))
             (left (car entry))
             (right (cadr entry)))
        (and
         (true-listp entry)
         (equal (len entry) 2)
         (ht021-member-p carrier left)
         (ht021-member-p carrier right)
         (ht021-in-interval-p less zero one left)
         (ht021-in-interval-p less zero one right)
         (ht021-leq-p less previous left)
         (ht021-less-p less left right)
         (ht021-interval-family-p
          carrier less zero one (cdr intervals) right)))
    (equal intervals nil)))

(defun ht021-interval-length-sum (add negate zero intervals)
  (if (consp intervals)
      (ht021-add
       add
       (ht021-sub add negate (cadar intervals) (caar intervals))
       (ht021-interval-length-sum add negate zero (cdr intervals)))
    zero))

(defun ht021-path-variation-sum
    (add negate less zero gx gy intervals)
  (if (consp intervals)
      (let* ((left (caar intervals))
             (right (cadar intervals))
             (dx (ht021-sub
                  add negate
                  (ht021-unary gx right)
                  (ht021-unary gx left)))
             (dy (ht021-sub
                  add negate
                  (ht021-unary gy right)
                  (ht021-unary gy left))))
        (ht021-add
         add
         (ht021-max less
                    (ht021-abs less negate zero dx)
                    (ht021-abs less negate zero dy))
         (ht021-path-variation-sum
          add negate less zero gx gy (cdr intervals))))
    zero))

(defun-sk ht021-ac-delta-p
    (carrier gx gy add negate zero one less epsilon delta)
  (forall (intervals)
    (implies
     (and
      (ht021-interval-family-p
       carrier less zero one intervals zero)
      (ht021-less-p
       less
       (ht021-interval-length-sum add negate zero intervals)
       delta))
     (ht021-less-p
      less
      (ht021-path-variation-sum
       add negate less zero gx gy intervals)
      epsilon))))

(defun-sk ht021-ac-radius-exists-p
    (carrier gx gy add negate zero one less epsilon)
  (exists (delta)
    (and
     (ht021-positive-p carrier less zero delta)
     (ht021-ac-delta-p
      carrier gx gy add negate zero one less epsilon delta))))

(defun-sk ht021-absolutely-continuous-path-p
    (carrier gx gy add negate zero one less)
  (forall (epsilon)
    (implies
     (ht021-positive-p carrier less zero epsilon)
     (ht021-ac-radius-exists-p
      carrier gx gy add negate zero one less epsilon))))

(defun ht021-closed-path-p (gx gy zero one)
  (and (equal (ht021-unary gx zero) (ht021-unary gx one))
       (equal (ht021-unary gy zero) (ht021-unary gy one))))

(defun-sk ht021-path-hits-point-p (gx gy zero one less x y)
  (exists (t0)
    (and
     (ht021-in-interval-p less zero one t0)
     (equal (ht021-unary gx t0) x)
     (equal (ht021-unary gy t0) y))))

;; Tagged divisions and gauge Riemann--Stieltjes sums.

(defun ht021-tagged-division-from-p
    (carrier less current finish entries)
  (if (consp entries)
      (let* ((entry (car entries))
             (left (car entry))
             (right (cadr entry))
             (tag (caddr entry)))
        (and
         (true-listp entry)
         (equal (len entry) 3)
         (equal left current)
         (ht021-member-p carrier right)
         (ht021-member-p carrier tag)
         (ht021-less-p less left right)
         (ht021-in-interval-p less left right tag)
         (ht021-tagged-division-from-p
          carrier less right finish (cdr entries))))
    (and (equal entries nil)
         (equal current finish))))

(defun ht021-tagged-division-p
    (carrier less start finish entries)
  (and
   (ht021-member-p carrier start)
   (ht021-member-p carrier finish)
   (ht021-tagged-division-from-p
    carrier less start finish entries)))

(defun-sk ht021-gauge-positive-on-p
    (carrier gauge less zero start finish)
  (forall (x)
    (implies
     (and (ht021-member-p carrier x)
          (ht021-in-interval-p less start finish x))
     (ht021-positive-p carrier less zero (ht021-unary gauge x)))))

(defun ht021-positive-gauge-on-p
    (carrier gauge less zero start finish)
  (and
   (ht021-valid-unary-function-p carrier gauge)
   (ht021-gauge-positive-on-p
    carrier gauge less zero start finish)))

(defun ht021-fine-tagged-division-p
    (add negate less gauge entries)
  (if (consp entries)
      (and
       (ht021-less-p
        less
        (ht021-sub add negate (cadar entries) (caar entries))
        (ht021-unary gauge (caddar entries)))
       (ht021-fine-tagged-division-p
        add negate less gauge (cdr entries)))
    (equal entries nil)))

(defun ht021-circulation-sum
    (add multiply negate zero p q gx gy entries)
  (if (consp entries)
      (let* ((entry (car entries))
             (left (car entry))
             (right (cadr entry))
             (tag (caddr entry))
             (x (ht021-unary gx tag))
             (y (ht021-unary gy tag))
             (dx (ht021-sub
                  add negate
                  (ht021-unary gx right)
                  (ht021-unary gx left)))
             (dy (ht021-sub
                  add negate
                  (ht021-unary gy right)
                  (ht021-unary gy left))))
        (ht021-add
         add
         (ht021-add
          add
          (ht021-mul multiply (ht021-binary p x y) dx)
          (ht021-mul multiply (ht021-binary q x y) dy))
         (ht021-circulation-sum
          add multiply negate zero p q gx gy (cdr entries))))
    zero))

(defun-sk ht021-circulation-close-for-gauge-p
    (carrier p q gx gy add multiply negate zero one less
             value epsilon gauge)
  (forall (entries)
    (implies
     (and
      (ht021-tagged-division-p carrier less zero one entries)
      (ht021-fine-tagged-division-p add negate less gauge entries))
     (ht021-less-p
      less
      (ht021-abs
       less negate zero
       (ht021-sub
        add negate
        (ht021-circulation-sum
         add multiply negate zero p q gx gy entries)
        value))
      epsilon))))

(defun-sk ht021-circulation-gauge-exists-p
    (carrier p q gx gy add multiply negate zero one less value epsilon)
  (exists (gauge)
    (and
     (tamep-functionp gauge)
     (ht021-positive-gauge-on-p
      carrier gauge less zero zero one)
     (ht021-circulation-close-for-gauge-p
      carrier p q gx gy add multiply negate zero one less
      value epsilon gauge))))

(defun-sk ht021-has-circulation-integral-p
    (carrier p q gx gy add multiply negate zero one less value)
  (forall (epsilon)
    (implies
     (ht021-positive-p carrier less zero epsilon)
     (ht021-circulation-gauge-exists-p
      carrier p q gx gy add multiply negate zero one less
      value epsilon))))

;; Pi is the gauge integral of 4/(1+x^2) on [0,1].

(defun ht021-pi-riemann-sum
    (add multiply negate inverse zero one entries)
  (if (consp entries)
      (let* ((left (caar entries))
             (right (cadar entries))
             (tag (caddar entries))
             (four (ht021-four add one))
             (denominator
              (ht021-add add one (ht021-square multiply tag)))
             (value
              (ht021-mul multiply four (ht021-inv inverse denominator)))
             (width (ht021-sub add negate right left)))
        (ht021-add
         add
         (ht021-mul multiply value width)
         (ht021-pi-riemann-sum
          add multiply negate inverse zero one (cdr entries))))
    zero))

(defun-sk ht021-pi-close-for-gauge-p
    (carrier add multiply negate inverse zero one less
             pi-value epsilon gauge)
  (forall (entries)
    (implies
     (and
      (ht021-tagged-division-p carrier less zero one entries)
      (ht021-fine-tagged-division-p add negate less gauge entries))
     (ht021-less-p
      less
      (ht021-abs
       less negate zero
       (ht021-sub
        add negate
        (ht021-pi-riemann-sum
         add multiply negate inverse zero one entries)
        pi-value))
      epsilon))))

(defun-sk ht021-pi-gauge-exists-p
    (carrier add multiply negate inverse zero one less pi-value epsilon)
  (exists (gauge)
    (and
     (tamep-functionp gauge)
     (ht021-positive-gauge-on-p
      carrier gauge less zero zero one)
     (ht021-pi-close-for-gauge-p
      carrier add multiply negate inverse zero one less
      pi-value epsilon gauge))))

(defun-sk ht021-pi-limit-p
    (carrier add multiply negate inverse zero one less pi-value)
  (forall (epsilon)
    (implies
     (ht021-positive-p carrier less zero epsilon)
     (ht021-pi-gauge-exists-p
      carrier add multiply negate inverse zero one less pi-value epsilon))))

(defun ht021-pi-p
    (carrier add multiply negate inverse zero one less pi-value)
  (and
   (ht021-member-p carrier pi-value)
   (ht021-pi-limit-p
    carrier add multiply negate inverse zero one less pi-value)))

;; Winding number one is the exact Riemann--Stieltjes identity
;; integral (-(g_y-y)/r^2) d g_x + ((g_x-x)/r^2) d g_y = 2*pi-value.

(defun ht021-winding-sum
    (add multiply negate inverse zero gx gy x y entries)
  (if (consp entries)
      (let* ((left (caar entries))
             (right (cadar entries))
             (tag (caddar entries))
             (rx (ht021-sub add negate (ht021-unary gx tag) x))
             (ry (ht021-sub add negate (ht021-unary gy tag) y))
             (radius-square
              (ht021-add
               add
               (ht021-square multiply rx)
               (ht021-square multiply ry)))
             (reciprocal (ht021-inv inverse radius-square))
             (dx (ht021-sub
                  add negate
                  (ht021-unary gx right)
                  (ht021-unary gx left)))
             (dy (ht021-sub
                  add negate
                  (ht021-unary gy right)
                  (ht021-unary gy left))))
        (ht021-add
         add
         (ht021-add
          add
          (ht021-mul
           multiply
           (ht021-neg
            negate (ht021-mul multiply ry reciprocal))
           dx)
          (ht021-mul
           multiply
           (ht021-mul multiply rx reciprocal)
           dy))
         (ht021-winding-sum
          add multiply negate inverse zero gx gy x y (cdr entries))))
    zero))

(defun-sk ht021-winding-close-for-gauge-p
    (carrier gx gy x y add multiply negate inverse zero one less
             value epsilon gauge)
  (forall (entries)
    (implies
     (and
      (ht021-tagged-division-p carrier less zero one entries)
      (ht021-fine-tagged-division-p add negate less gauge entries))
     (ht021-less-p
      less
      (ht021-abs
       less negate zero
       (ht021-sub
        add negate
        (ht021-winding-sum
         add multiply negate inverse zero gx gy x y entries)
        value))
      epsilon))))

(defun-sk ht021-winding-gauge-exists-p
    (carrier gx gy x y add multiply negate inverse zero one less
             value epsilon)
  (exists (gauge)
    (and
     (tamep-functionp gauge)
     (ht021-positive-gauge-on-p
      carrier gauge less zero zero one)
     (ht021-winding-close-for-gauge-p
      carrier gx gy x y add multiply negate inverse zero one less
      value epsilon gauge))))

(defun-sk ht021-has-winding-integral-p
    (carrier gx gy x y add multiply negate inverse zero one less value)
  (forall (epsilon)
    (implies
     (ht021-positive-p carrier less zero epsilon)
     (ht021-winding-gauge-exists-p
      carrier gx gy x y add multiply negate inverse zero one less
      value epsilon))))

(defun ht021-winding-one-p
    (carrier gx gy x y pi-value add multiply negate inverse zero one less)
  (let ((two-pi (ht021-mul multiply (ht021-two add one) pi-value)))
    (and
     (ht021-member-p carrier x)
     (ht021-member-p carrier y)
     (not (ht021-path-hits-point-p gx gy zero one less x y))
     (ht021-has-winding-integral-p
      carrier gx gy x y add multiply negate inverse zero one less
      two-pi))))

;; The HOL source's INSIDE(path_image g) is the union of the bounded
;; components of the complement. For a compact planar path image, a
;; complementary point is in the unbounded component exactly when it can be
;; joined through the complement to a point outside a square containing the
;; image. The following definitions therefore express, without an opaque
;; region parameter, the source assumption that winding number is one at
;; every point of INSIDE(path_image g).

(defun-sk ht021-path-image-in-square-p
    (carrier gx gy zero one less negate bound)
  (forall (parameter)
    (implies
     (and
      (ht021-member-p carrier parameter)
      (ht021-in-interval-p less zero one parameter))
     (and
      (ht021-leq-p
       less
       (ht021-abs
        less negate zero (ht021-unary gx parameter))
       bound)
      (ht021-leq-p
       less
       (ht021-abs
        less negate zero (ht021-unary gy parameter))
       bound)))))

(defun-sk ht021-continuity-neighborhood-p
    (carrier hx hy add negate zero one less
             parameter epsilon delta)
  (forall (other)
    (implies
     (and
      (ht021-member-p carrier other)
      (ht021-in-interval-p less zero one other)
      (ht021-less-p
       less
       (ht021-abs
        less negate zero
        (ht021-sub add negate other parameter))
       delta))
     (ht021-less-p
      less
      (ht021-plane-distance
       add negate less zero
       (ht021-unary hx other)
       (ht021-unary hy other)
       (ht021-unary hx parameter)
       (ht021-unary hy parameter))
      epsilon))))

(defun-sk ht021-continuity-radius-exists-p
    (carrier hx hy add negate zero one less parameter epsilon)
  (exists (delta)
    (and
     (ht021-positive-p carrier less zero delta)
     (ht021-continuity-neighborhood-p
      carrier hx hy add negate zero one less
      parameter epsilon delta))))

(defun-sk ht021-continuous-planar-path-p
    (carrier hx hy add negate zero one less)
  (forall (parameter epsilon)
    (implies
     (and
      (ht021-member-p carrier parameter)
      (ht021-in-interval-p less zero one parameter)
      (ht021-positive-p carrier less zero epsilon))
     (ht021-continuity-radius-exists-p
      carrier hx hy add negate zero one less parameter epsilon))))

(defun-sk ht021-connector-avoids-image-p
    (carrier gx gy hx hy zero one less)
  (forall (parameter)
    (implies
     (and
      (ht021-member-p carrier parameter)
      (ht021-in-interval-p less zero one parameter))
     (not
      (ht021-path-hits-point-p
       gx gy zero one less
       (ht021-unary hx parameter)
       (ht021-unary hy parameter))))))

(defun ht021-outside-connector-p
    (carrier gx gy hx hy x y bound
             add negate zero one less)
  (and
   (ht021-valid-unary-function-p carrier hx)
   (ht021-valid-unary-function-p carrier hy)
   (ht021-continuous-planar-path-p
    carrier hx hy add negate zero one less)
   (equal (ht021-unary hx zero) x)
   (equal (ht021-unary hy zero) y)
   (or
    (ht021-less-p
     less bound
     (ht021-abs less negate zero (ht021-unary hx one)))
    (ht021-less-p
     less bound
     (ht021-abs less negate zero (ht021-unary hy one))))
   (ht021-connector-avoids-image-p
    carrier gx gy hx hy zero one less)))

(defun-sk ht021-outside-connector-exists-p
    (carrier gx gy x y bound add negate zero one less)
  (exists (hx hy)
    (ht021-outside-connector-p
     carrier gx gy hx hy x y bound
     add negate zero one less)))

(defun-sk ht021-complement-classified-at-bound-p
    (carrier gx gy pi-value bound
             add multiply negate inverse zero one less)
  (forall (x y)
    (implies
     (and
      (ht021-member-p carrier x)
      (ht021-member-p carrier y)
      (not (ht021-path-hits-point-p gx gy zero one less x y)))
     (or
      (ht021-winding-one-p
       carrier gx gy x y pi-value
       add multiply negate inverse zero one less)
      (ht021-outside-connector-exists-p
       carrier gx gy x y bound add negate zero one less)))))

(defun-sk ht021-positive-interior-orientation-p
    (carrier gx gy pi-value
             add multiply negate inverse zero one less)
  (exists (bound)
    (and
     (ht021-positive-p carrier less zero bound)
     (ht021-path-image-in-square-p
      carrier gx gy zero one less negate bound)
     (ht021-complement-classified-at-bound-p
      carrier gx gy pi-value bound
      add multiply negate inverse zero one less))))

;; Open neighborhood and local C1 hypotheses.

(defun-sk ht021-open-ball-contained-p
    (carrier neighborhood add negate zero less x y radius)
  (forall (u v)
    (implies
     (and
      (ht021-member-p carrier u)
      (ht021-member-p carrier v)
      (ht021-less-p
       less
       (ht021-plane-distance add negate less zero x y u v)
       radius))
     (apply$ neighborhood (list u v)))))

(defun-sk ht021-open-radius-exists-p
    (carrier neighborhood add negate zero less x y)
  (exists (radius)
    (and
     (ht021-positive-p carrier less zero radius)
     (ht021-open-ball-contained-p
      carrier neighborhood add negate zero less x y radius))))

(defun-sk ht021-open-set-p
    (carrier neighborhood add negate zero less)
  (forall (x y)
    (implies
     (and
      (ht021-member-p carrier x)
      (ht021-member-p carrier y)
      (apply$ neighborhood (list x y)))
     (ht021-open-radius-exists-p
      carrier neighborhood add negate zero less x y))))

(defun-sk ht021-neighborhood-contains-relevant-p
    (carrier neighborhood gx gy pi-value
             add multiply negate inverse zero one less)
  (forall (x y)
    (implies
     (and
      (ht021-member-p carrier x)
      (ht021-member-p carrier y)
      (or
       (ht021-path-hits-point-p gx gy zero one less x y)
       (ht021-winding-one-p
        carrier gx gy x y pi-value
        add multiply negate inverse zero one less)))
     (apply$ neighborhood (list x y)))))

(defun ht021-derivative-residual
    (function x-derivative y-derivative
              add multiply negate x y dx dy)
  (ht021-sub
   add negate
   (ht021-sub
    add negate
    (ht021-binary
     function (ht021-add add x dx) (ht021-add add y dy))
    (ht021-binary function x y))
   (ht021-add
    add
    (ht021-mul multiply (ht021-binary x-derivative x y) dx)
    (ht021-mul multiply (ht021-binary y-derivative x y) dy))))

(defun-sk ht021-frechet-neighborhood-p
    (carrier neighborhood function x-derivative y-derivative
             add multiply negate zero less x y epsilon delta)
  (forall (dx dy)
    (implies
     (and
      (ht021-member-p carrier dx)
      (ht021-member-p carrier dy)
      (apply$ neighborhood
              (list (ht021-add add x dx) (ht021-add add y dy)))
      (ht021-less-p
       less
       (ht021-plane-distance add negate less zero zero zero dx dy)
       delta))
     (ht021-leq-p
      less
      (ht021-abs
       less negate zero
       (ht021-derivative-residual
        function x-derivative y-derivative
        add multiply negate x y dx dy))
      (ht021-mul
       multiply epsilon
       (ht021-plane-distance
        add negate less zero zero zero dx dy))))))

(defun-sk ht021-frechet-radius-exists-p
    (carrier neighborhood function x-derivative y-derivative
             add multiply negate zero less x y epsilon)
  (exists (delta)
    (and
     (ht021-positive-p carrier less zero delta)
     (ht021-frechet-neighborhood-p
      carrier neighborhood function x-derivative y-derivative
      add multiply negate zero less x y epsilon delta))))

(defun-sk ht021-has-frechet-derivative-at-p
    (carrier neighborhood function x-derivative y-derivative
             add multiply negate zero less x y)
  (forall (epsilon)
    (implies
     (ht021-positive-p carrier less zero epsilon)
     (ht021-frechet-radius-exists-p
      carrier neighborhood function x-derivative y-derivative
      add multiply negate zero less x y epsilon))))

(defun-sk ht021-differentiable-on-p
    (carrier neighborhood function x-derivative y-derivative
             add multiply negate zero less)
  (forall (x y)
    (implies
     (and
      (ht021-member-p carrier x)
      (ht021-member-p carrier y)
      (apply$ neighborhood (list x y)))
     (ht021-has-frechet-derivative-at-p
      carrier neighborhood function x-derivative y-derivative
      add multiply negate zero less x y))))

(defun-sk ht021-derivative-continuous-neighborhood-p
    (carrier neighborhood x-derivative y-derivative
             add negate zero less x y epsilon delta)
  (forall (u v)
    (implies
     (and
      (ht021-member-p carrier u)
      (ht021-member-p carrier v)
      (apply$ neighborhood (list u v))
      (ht021-less-p
       less
       (ht021-plane-distance add negate less zero x y u v)
       delta))
     (and
      (ht021-less-p
       less
       (ht021-abs
        less negate zero
        (ht021-sub
         add negate
         (ht021-binary x-derivative u v)
         (ht021-binary x-derivative x y)))
       epsilon)
      (ht021-less-p
       less
       (ht021-abs
        less negate zero
        (ht021-sub
         add negate
         (ht021-binary y-derivative u v)
         (ht021-binary y-derivative x y)))
       epsilon)))))

(defun-sk ht021-derivative-continuity-radius-p
    (carrier neighborhood x-derivative y-derivative
             add negate zero less x y epsilon)
  (exists (delta)
    (and
     (ht021-positive-p carrier less zero delta)
     (ht021-derivative-continuous-neighborhood-p
      carrier neighborhood x-derivative y-derivative
      add negate zero less x y epsilon delta))))

(defun-sk ht021-derivative-pair-continuous-on-p
    (carrier neighborhood x-derivative y-derivative
             add negate zero less)
  (forall (x y epsilon)
    (implies
     (and
      (ht021-member-p carrier x)
      (ht021-member-p carrier y)
      (apply$ neighborhood (list x y))
      (ht021-positive-p carrier less zero epsilon))
     (ht021-derivative-continuity-radius-p
      carrier neighborhood x-derivative y-derivative
      add negate zero less x y epsilon))))

(defun ht021-c1-on-p
    (carrier neighborhood function x-derivative y-derivative
             add multiply negate zero less)
  (and
   (tamep-functionp x-derivative)
   (tamep-functionp y-derivative)
   (ht021-valid-binary-function-p carrier x-derivative)
   (ht021-valid-binary-function-p carrier y-derivative)
   (ht021-differentiable-on-p
    carrier neighborhood function x-derivative y-derivative
    add multiply negate zero less)
   (ht021-derivative-pair-continuous-on-p
    carrier neighborhood x-derivative y-derivative
    add negate zero less)))

(defun-sk ht021-field-c1-witness-p
    (carrier neighborhood p q add multiply negate zero less)
  (exists (p-x p-y q-x q-y)
    (and
     (ht021-c1-on-p
      carrier neighborhood p p-x p-y
      add multiply negate zero less)
     (ht021-c1-on-p
      carrier neighborhood q q-x q-y
      add multiply negate zero less))))

;; Two-dimensional gauge integration over a square containing the
;; winding-one region. Every rectangular cell has an arbitrary tag.

(defun ht021-division-from-p (carrier less current finish cells)
  (if (consp cells)
      (let* ((cell (car cells))
             (left (car cell))
             (right (cadr cell)))
        (and
         (true-listp cell)
         (equal (len cell) 2)
         (equal left current)
         (ht021-member-p carrier right)
         (ht021-less-p less left right)
         (ht021-division-from-p
          carrier less right finish (cdr cells))))
    (and (equal cells nil)
         (equal current finish))))

(defun ht021-division-p (carrier less start finish cells)
  (ht021-division-from-p carrier less start finish cells))

(defun ht021-tags-fit-row-p (carrier less xcell ycells tags)
  (if (consp ycells)
      (and
       (consp tags)
       (true-listp (car tags))
       (equal (len (car tags)) 2)
       (ht021-member-p carrier (caar tags))
       (ht021-member-p carrier (cadar tags))
       (ht021-in-interval-p
        less (car xcell) (cadr xcell) (caar tags))
       (ht021-in-interval-p
        less (caar ycells) (cadar ycells) (cadar tags))
       (ht021-tags-fit-row-p
        carrier less xcell (cdr ycells) (cdr tags)))
    (equal tags nil)))

(defun ht021-tags-fit-grid-p
    (carrier less xcells ycells tags)
  (if (consp xcells)
      (and
       (consp tags)
       (ht021-tags-fit-row-p
        carrier less (car xcells) ycells (car tags))
       (ht021-tags-fit-grid-p
        carrier less (cdr xcells) ycells (cdr tags)))
    (equal tags nil)))

(defun-sk ht021-bivariate-gauge-positive-on-square-p
    (carrier gauge negate less zero bound)
  (forall (x y)
    (implies
     (and
      (ht021-member-p carrier x)
      (ht021-member-p carrier y)
      (ht021-in-interval-p less (ht021-neg negate bound) bound x)
      (ht021-in-interval-p less (ht021-neg negate bound) bound y))
     (ht021-positive-p
      carrier less zero (ht021-binary gauge x y)))))

(defun ht021-grid-fine-row-p
    (add negate less gauge xcell ycells tags)
  (if (consp ycells)
      (let* ((ycell (car ycells))
             (tag (car tags))
             (xwidth
              (ht021-sub add negate (cadr xcell) (car xcell)))
             (ywidth
              (ht021-sub add negate (cadr ycell) (car ycell)))
             (mesh (ht021-max less xwidth ywidth))
             (radius (ht021-binary gauge (car tag) (cadr tag))))
        (and
         (ht021-less-p less mesh radius)
         (ht021-grid-fine-row-p
          add negate less gauge xcell (cdr ycells) (cdr tags))))
    t))

(defun ht021-grid-fine-p
    (add negate less gauge xcells ycells tags)
  (if (consp xcells)
      (and
       (ht021-grid-fine-row-p
        add negate less gauge (car xcells) ycells (car tags))
       (ht021-grid-fine-p
        add negate less gauge (cdr xcells) ycells (cdr tags)))
    t))

(defun ht021-curl-at (add negate p-y q-x x y)
  (ht021-sub
   add negate
   (ht021-binary q-x x y)
   (ht021-binary p-y x y)))

(defun ht021-region-sum-row
    (carrier gx gy pi-value p-y q-x
             add multiply negate inverse zero one less
             xcell ycells tags)
  (if (consp ycells)
      (let* ((ycell (car ycells))
             (tag (car tags))
             (x (car tag))
             (y (cadr tag))
             (xwidth
              (ht021-sub add negate (cadr xcell) (car xcell)))
             (ywidth
              (ht021-sub add negate (cadr ycell) (car ycell)))
             (area (ht021-mul multiply xwidth ywidth))
             (value
              (if
                  (ht021-winding-one-p
                   carrier gx gy x y pi-value
                   add multiply negate inverse zero one less)
                  (ht021-curl-at add negate p-y q-x x y)
                zero)))
        (ht021-add
         add
         (ht021-mul multiply value area)
         (ht021-region-sum-row
          carrier gx gy pi-value p-y q-x
          add multiply negate inverse zero one less
          xcell (cdr ycells) (cdr tags))))
    zero))

(defun ht021-region-sum
    (carrier gx gy pi-value p-y q-x
             add multiply negate inverse zero one less
             xcells ycells tags)
  (if (consp xcells)
      (ht021-add
       add
       (ht021-region-sum-row
        carrier gx gy pi-value p-y q-x
        add multiply negate inverse zero one less
        (car xcells) ycells (car tags))
       (ht021-region-sum
        carrier gx gy pi-value p-y q-x
        add multiply negate inverse zero one less
        (cdr xcells) ycells (cdr tags)))
    zero))

(defun-sk ht021-region-contained-in-square-p
    (carrier gx gy pi-value add multiply negate inverse zero one less bound)
  (forall (x y)
    (implies
     (ht021-winding-one-p
      carrier gx gy x y pi-value
      add multiply negate inverse zero one less)
     (and
      (ht021-leq-p less (ht021-abs less negate zero x) bound)
      (ht021-leq-p less (ht021-abs less negate zero y) bound)))))

(defun-sk ht021-region-close-for-gauge-p
    (carrier gx gy pi-value p-y q-x
             add multiply negate inverse zero one less
             bound value epsilon gauge)
  (forall (xcells ycells tags)
    (implies
     (and
      (ht021-division-p
       carrier less (ht021-neg negate bound) bound xcells)
      (ht021-division-p
       carrier less (ht021-neg negate bound) bound ycells)
      (ht021-tags-fit-grid-p
       carrier less xcells ycells tags)
      (ht021-grid-fine-p
       add negate less gauge xcells ycells tags))
     (ht021-less-p
      less
      (ht021-abs
       less negate zero
       (ht021-sub
        add negate
        (ht021-region-sum
         carrier gx gy pi-value p-y q-x
         add multiply negate inverse zero one less
         xcells ycells tags)
        value))
      epsilon))))

(defun-sk ht021-region-gauge-exists-p
    (carrier gx gy pi-value p-y q-x
             add multiply negate inverse zero one less
             bound value epsilon)
  (exists (gauge)
    (and
     (tamep-functionp gauge)
     (ht021-valid-binary-function-p carrier gauge)
     (ht021-bivariate-gauge-positive-on-square-p
      carrier gauge negate less zero bound)
     (ht021-region-close-for-gauge-p
      carrier gx gy pi-value p-y q-x
      add multiply negate inverse zero one less
      bound value epsilon gauge))))

(defun-sk ht021-region-integral-at-bound-p
    (carrier gx gy pi-value p-y q-x
             add multiply negate inverse zero one less bound value)
  (forall (epsilon)
    (implies
     (ht021-positive-p carrier less zero epsilon)
     (ht021-region-gauge-exists-p
      carrier gx gy pi-value p-y q-x
      add multiply negate inverse zero one less
      bound value epsilon))))

(defun-sk ht021-has-region-integral-p
    (carrier gx gy pi-value p-y q-x
             add multiply negate inverse zero one less value)
  (exists (bound)
    (and
     (ht021-positive-p carrier less zero bound)
     (ht021-region-contained-in-square-p
      carrier gx gy pi-value
      add multiply negate inverse zero one less bound)
     (ht021-region-integral-at-bound-p
      carrier gx gy pi-value p-y q-x
      add multiply negate inverse zero one less bound value))))

;; Derivative and integral values are internal witnesses constrained by the
;; definitions above; the desired equality is not an input assumption.

(defun-sk ht021-green-conclusion-p
    (carrier neighborhood p q gx gy pi-value
             add multiply negate inverse zero one less)
  (exists (p-x p-y q-x q-y circulation curl-integral)
    (and
     (ht021-member-p carrier circulation)
     (ht021-member-p carrier curl-integral)
     (ht021-c1-on-p
      carrier neighborhood p p-x p-y
      add multiply negate zero less)
     (ht021-c1-on-p
      carrier neighborhood q q-x q-y
      add multiply negate zero less)
     (ht021-has-circulation-integral-p
      carrier p q gx gy add multiply negate zero one less circulation)
     (ht021-has-region-integral-p
      carrier gx gy pi-value p-y q-x
      add multiply negate inverse zero one less curl-integral)
     (equal circulation curl-integral))))

(defun hundred-theorems-021-greens-theorem-statement
    (carrier add multiply negate inverse zero one less
             p q gx gy neighborhood pi-value)
  (implies
   (and
    (ht021-real-field-p
     carrier add multiply negate inverse zero one less)
    (ht021-valid-binary-function-p carrier p)
    (ht021-valid-binary-function-p carrier q)
    (ht021-valid-unary-function-p carrier gx)
    (ht021-valid-unary-function-p carrier gy)
    (tamep-functionp neighborhood)
    (ht021-pi-p
     carrier add multiply negate inverse zero one less pi-value)
    (ht021-absolutely-continuous-path-p
     carrier gx gy add negate zero one less)
    (ht021-closed-path-p gx gy zero one)
    (ht021-positive-interior-orientation-p
     carrier gx gy pi-value
     add multiply negate inverse zero one less)
    (ht021-open-set-p
     carrier neighborhood add negate zero less)
    (ht021-neighborhood-contains-relevant-p
     carrier neighborhood gx gy pi-value
     add multiply negate inverse zero one less)
    (ht021-field-c1-witness-p
     carrier neighborhood p q add multiply negate zero less))
   (ht021-green-conclusion-p
    carrier neighborhood p q gx gy pi-value
    add multiply negate inverse zero one less)))

(value-triple :itpeval-statement-checked)
:q
