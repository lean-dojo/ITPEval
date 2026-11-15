;; Statement-only formalization of Hundred Theorems artifact 013,
;; "Polyhedron Formula." Every full-dimensional convex polytope in
;; three-dimensional real space has V + F = E + 2. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; ACL2's built-in numbers are not the real numbers, so the scalar structure
;; is an explicit real-closed ordered field. Real closedness is the
;; first-order algebraic theory of the reals needed by this statement.

(defstub ht013-carrier (x) t)
(defstub ht013-add-op (x y) t)
(defstub ht013-multiply-op (x y) t)
(defstub ht013-negate-op (x) t)
(defstub ht013-inverse-op (x) t)
(defstub ht013-less-op (x y) t)

(defun ht013-member-p (x)
  (if (ht013-carrier x) t nil))

(defun ht013-add (x y)
  (ht013-add-op x y))

(defun ht013-multiply (x y)
  (ht013-multiply-op x y))

(defun ht013-negate (x)
  (ht013-negate-op x))

(defun ht013-inverse (x)
  (ht013-inverse-op x))

(defun ht013-subtract (x y)
  (ht013-add x (ht013-negate y)))

(defun ht013-less (x y)
  (if (ht013-less-op x y) t nil))

(defun ht013-less-or-equal (x y)
  (or (equal x y)
      (ht013-less x y)))

(defun ht013-square (x)
  (ht013-multiply x x))

(defun-sk ht013-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht013-member-p x)
      (ht013-member-p y)
      (ht013-member-p z))
     (and
      (ht013-member-p (ht013-add x y))
      (ht013-member-p (ht013-multiply x y))
      (ht013-member-p (ht013-negate x))
      (ht013-member-p (ht013-inverse x))
      (equal (ht013-add (ht013-add x y) z)
             (ht013-add x (ht013-add y z)))
      (equal (ht013-add x y)
             (ht013-add y x))
      (equal (ht013-add x zero) x)
      (equal (ht013-add x (ht013-negate x)) zero)
      (equal (ht013-multiply (ht013-multiply x y) z)
             (ht013-multiply x (ht013-multiply y z)))
      (equal (ht013-multiply x y)
             (ht013-multiply y x))
      (equal (ht013-multiply x one) x)
      (equal
       (ht013-multiply x (ht013-add y z))
       (ht013-add
        (ht013-multiply x y)
        (ht013-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht013-multiply x (ht013-inverse x))
        one))))))

(defun-sk ht013-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht013-member-p x)
      (ht013-member-p y)
      (ht013-member-p z))
     (and
      (not (ht013-less x x))
      (or
       (equal x y)
       (ht013-less x y)
       (ht013-less y x))
      (implies
       (and
        (ht013-less x y)
        (ht013-less y z))
       (ht013-less x z))
      (implies
       (ht013-less x y)
       (ht013-less
        (ht013-add x z)
        (ht013-add y z)))
      (implies
       (and
        (ht013-less zero x)
        (ht013-less zero y))
       (ht013-less zero (ht013-multiply x y)))))))

(defun ht013-field-list-p (values)
  (if (consp values)
      (and
       (ht013-member-p (car values))
       (ht013-field-list-p (cdr values)))
    (equal values nil)))

(defun ht013-polynomial-value (coefficients x zero)
  (if (consp coefficients)
      (ht013-add
       (car coefficients)
       (ht013-multiply
        x
        (ht013-polynomial-value (cdr coefficients) x zero)))
    zero))

(defun ht013-odd-degree-polynomial-p (coefficients zero)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht013-field-list-p coefficients)
   (evenp (len coefficients))
   (not (equal (car (last coefficients)) zero))))

(defun-sk ht013-has-square-root-p (x zero)
  (exists (root)
    (and
     (ht013-member-p root)
     (equal (ht013-square root) x))))

(defun-sk ht013-has-polynomial-root-p (coefficients zero)
  (exists (root)
    (and
     (ht013-member-p root)
     (equal
      (ht013-polynomial-value coefficients root zero)
      zero))))

(defun-sk ht013-real-closure-laws-p (zero)
  (forall (x coefficients)
    (and
     (implies
      (and
       (ht013-member-p x)
       (not (ht013-less x zero)))
      (ht013-has-square-root-p x zero))
     (implies
      (ht013-odd-degree-polynomial-p coefficients zero)
      (ht013-has-polynomial-root-p coefficients zero)))))

(defun ht013-real-scalar-context-p (zero one)
  (and
   (ht013-member-p zero)
   (ht013-member-p one)
   (not (equal zero one))
   (ht013-less zero one)
   (ht013-field-laws-p zero one)
   (ht013-order-laws-p zero)
   (ht013-real-closure-laws-p zero)))

;; A point is the proper list (x y z), and a plane is the proper list
;; (a b c d), denoting a*x + b*y + c*z = d. A polytope is represented by a
;; finite list of planes whose corresponding closed half-spaces are
;; intersected.

(defun ht013-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (ht013-member-p (nth 0 point))
   (ht013-member-p (nth 1 point))
   (ht013-member-p (nth 2 point))))

(defun ht013-point-x (point)
  (nth 0 point))

(defun ht013-point-y (point)
  (nth 1 point))

(defun ht013-point-z (point)
  (nth 2 point))

(defun ht013-plane-p (plane zero)
  (and
   (true-listp plane)
   (equal (len plane) 4)
   (ht013-member-p (nth 0 plane))
   (ht013-member-p (nth 1 plane))
   (ht013-member-p (nth 2 plane))
   (ht013-member-p (nth 3 plane))
   (not
    (and
     (equal (nth 0 plane) zero)
     (equal (nth 1 plane) zero)
     (equal (nth 2 plane) zero)))))

(defun ht013-plane-value (plane point)
  (ht013-add
   (ht013-add
    (ht013-multiply (nth 0 plane) (ht013-point-x point))
    (ht013-multiply (nth 1 plane) (ht013-point-y point)))
   (ht013-multiply (nth 2 plane) (ht013-point-z point))))

(defun ht013-plane-bound (plane)
  (nth 3 plane))

(defun ht013-halfspace-list-p (halfspaces zero)
  (if (consp halfspaces)
      (and
       (ht013-plane-p (car halfspaces) zero)
       (ht013-halfspace-list-p (cdr halfspaces) zero))
    (equal halfspaces nil)))

(defun ht013-point-in-polytope-p (point halfspaces)
  (and
   (ht013-point-p point)
   (if (consp halfspaces)
       (and
        (ht013-less-or-equal
         (ht013-plane-value (car halfspaces) point)
         (ht013-plane-bound (car halfspaces)))
        (ht013-point-in-polytope-p point (cdr halfspaces)))
     (equal halfspaces nil))))

(defun ht013-coordinate-bounded-p (coordinate bound)
  (and
   (ht013-less-or-equal (ht013-negate bound) coordinate)
   (ht013-less-or-equal coordinate bound)))

(defun-sk ht013-bound-works-p (halfspaces bound)
  (forall (point)
    (implies
     (ht013-point-in-polytope-p point halfspaces)
     (and
      (ht013-coordinate-bounded-p (ht013-point-x point) bound)
      (ht013-coordinate-bounded-p (ht013-point-y point) bound)
      (ht013-coordinate-bounded-p (ht013-point-z point) bound)))))

(defun-sk ht013-bounded-p (halfspaces zero)
  (exists (bound)
    (and
     (ht013-member-p bound)
     (ht013-less zero bound)
     (ht013-bound-works-p halfspaces bound))))

(defun ht013-distance-squared (first second)
  (let ((dx (ht013-subtract
             (ht013-point-x first)
             (ht013-point-x second)))
        (dy (ht013-subtract
             (ht013-point-y first)
             (ht013-point-y second)))
        (dz (ht013-subtract
             (ht013-point-z first)
             (ht013-point-z second))))
    (ht013-add
     (ht013-add (ht013-square dx) (ht013-square dy))
     (ht013-square dz))))

(defun-sk ht013-open-ball-contained-p (halfspaces center radius)
  (forall (point)
    (implies
     (and
      (ht013-point-p point)
      (ht013-less
       (ht013-distance-squared point center)
       (ht013-square radius)))
     (ht013-point-in-polytope-p point halfspaces))))

(defun-sk ht013-full-dimensional-p (halfspaces zero)
  (exists (center radius)
    (and
     (ht013-point-p center)
     (ht013-member-p radius)
     (ht013-less zero radius)
     (ht013-open-ball-contained-p halfspaces center radius))))

(defun ht013-polytope3-p (halfspaces zero)
  (and
   (true-listp halfspaces)
   (ht013-halfspace-list-p halfspaces zero)
   (ht013-bounded-p halfspaces zero)
   (ht013-full-dimensional-p halfspaces zero)))

;; Every face of a polytope is exposed. A plane descriptor represents the
;; nonempty face where a supporting inequality is tight.

(defun-sk ht013-supporting-plane-p (halfspaces plane)
  (forall (point)
    (implies
     (ht013-point-in-polytope-p point halfspaces)
     (ht013-less-or-equal
      (ht013-plane-value plane point)
      (ht013-plane-bound plane)))))

(defun ht013-point-in-face-p (point halfspaces plane)
  (and
   (ht013-point-in-polytope-p point halfspaces)
   (equal
    (ht013-plane-value plane point)
    (ht013-plane-bound plane))))

(defun-sk ht013-face-equivalent-p
    (halfspaces first-plane second-plane)
  (forall (point)
    (equal
     (ht013-point-in-face-p point halfspaces first-plane)
     (ht013-point-in-face-p point halfspaces second-plane))))

;; Affine dimensions zero, one, and two are expressed intrinsically. The
;; quantified scalars in on-line and on-plane range over the field carrier.

(defun-sk ht013-on-line-p (point first second)
  (exists (parameter)
    (and
     (ht013-member-p parameter)
     (equal
      (ht013-point-x point)
      (ht013-add
       (ht013-point-x first)
       (ht013-multiply
        parameter
        (ht013-subtract
         (ht013-point-x second)
         (ht013-point-x first)))))
     (equal
      (ht013-point-y point)
      (ht013-add
       (ht013-point-y first)
       (ht013-multiply
        parameter
        (ht013-subtract
         (ht013-point-y second)
         (ht013-point-y first)))))
     (equal
      (ht013-point-z point)
      (ht013-add
       (ht013-point-z first)
       (ht013-multiply
        parameter
        (ht013-subtract
         (ht013-point-z second)
         (ht013-point-z first))))))))

(defun ht013-cross-x (first second third)
  (ht013-subtract
   (ht013-multiply
    (ht013-subtract (ht013-point-y second) (ht013-point-y first))
    (ht013-subtract (ht013-point-z third) (ht013-point-z first)))
   (ht013-multiply
    (ht013-subtract (ht013-point-z second) (ht013-point-z first))
    (ht013-subtract (ht013-point-y third) (ht013-point-y first)))))

(defun ht013-cross-y (first second third)
  (ht013-subtract
   (ht013-multiply
    (ht013-subtract (ht013-point-z second) (ht013-point-z first))
    (ht013-subtract (ht013-point-x third) (ht013-point-x first)))
   (ht013-multiply
    (ht013-subtract (ht013-point-x second) (ht013-point-x first))
    (ht013-subtract (ht013-point-z third) (ht013-point-z first)))))

(defun ht013-cross-z (first second third)
  (ht013-subtract
   (ht013-multiply
    (ht013-subtract (ht013-point-x second) (ht013-point-x first))
    (ht013-subtract (ht013-point-y third) (ht013-point-y first)))
   (ht013-multiply
    (ht013-subtract (ht013-point-y second) (ht013-point-y first))
    (ht013-subtract (ht013-point-x third) (ht013-point-x first)))))

(defun ht013-affinely-independent-three-p
    (first second third zero)
  (or
   (not (equal (ht013-cross-x first second third) zero))
   (not (equal (ht013-cross-y first second third) zero))
   (not (equal (ht013-cross-z first second third) zero))))

(defun-sk ht013-on-plane-p (point first second third)
  (exists (first-parameter second-parameter)
    (and
     (ht013-member-p first-parameter)
     (ht013-member-p second-parameter)
     (equal
      (ht013-point-x point)
      (ht013-add
       (ht013-add
        (ht013-point-x first)
        (ht013-multiply
         first-parameter
         (ht013-subtract
          (ht013-point-x second)
          (ht013-point-x first))))
       (ht013-multiply
        second-parameter
        (ht013-subtract
         (ht013-point-x third)
         (ht013-point-x first)))))
     (equal
      (ht013-point-y point)
      (ht013-add
       (ht013-add
        (ht013-point-y first)
        (ht013-multiply
         first-parameter
         (ht013-subtract
          (ht013-point-y second)
          (ht013-point-y first))))
       (ht013-multiply
        second-parameter
        (ht013-subtract
         (ht013-point-y third)
         (ht013-point-y first)))))
     (equal
      (ht013-point-z point)
      (ht013-add
       (ht013-add
        (ht013-point-z first)
        (ht013-multiply
         first-parameter
         (ht013-subtract
          (ht013-point-z second)
          (ht013-point-z first))))
       (ht013-multiply
        second-parameter
        (ht013-subtract
         (ht013-point-z third)
         (ht013-point-z first))))))))

(defun-sk ht013-face-is-singleton-p
    (halfspaces plane point)
  (forall (other)
    (implies
     (ht013-point-in-face-p other halfspaces plane)
     (equal other point))))

(defun-sk ht013-face-dimension-zero-p
    (halfspaces plane)
  (exists (point)
    (and
     (ht013-point-in-face-p point halfspaces plane)
     (ht013-face-is-singleton-p halfspaces plane point))))

(defun-sk ht013-face-contained-in-line-p
    (halfspaces plane first second)
  (forall (point)
    (implies
     (ht013-point-in-face-p point halfspaces plane)
     (ht013-on-line-p point first second))))

(defun-sk ht013-face-dimension-one-p
    (halfspaces plane)
  (exists (first second)
    (and
     (ht013-point-in-face-p first halfspaces plane)
     (ht013-point-in-face-p second halfspaces plane)
     (not (equal first second))
     (ht013-face-contained-in-line-p
      halfspaces plane first second))))

(defun-sk ht013-face-contained-in-plane-p
    (halfspaces plane first second third)
  (forall (point)
    (implies
     (ht013-point-in-face-p point halfspaces plane)
     (ht013-on-plane-p point first second third))))

(defun-sk ht013-face-dimension-two-p
    (halfspaces plane zero)
  (exists (first second third)
    (and
     (ht013-point-in-face-p first halfspaces plane)
     (ht013-point-in-face-p second halfspaces plane)
     (ht013-point-in-face-p third halfspaces plane)
     (ht013-affinely-independent-three-p
      first second third zero)
     (ht013-face-contained-in-plane-p
      halfspaces plane first second third))))

(defun ht013-face-of-dimension-p
    (halfspaces plane dimension zero)
  (and
   (ht013-plane-p plane zero)
   (ht013-supporting-plane-p halfspaces plane)
   (cond
    ((equal dimension 0)
     (ht013-face-dimension-zero-p halfspaces plane))
    ((equal dimension 1)
     (ht013-face-dimension-one-p halfspaces plane))
    ((equal dimension 2)
     (ht013-face-dimension-two-p halfspaces plane zero))
    (t nil))))

;; A finite list enumerates the faces of one dimension when every descriptor
;; is sound, no two descriptors denote the same face, and every supporting
;; plane for such a face is extensionally represented in the list.

(defun ht013-equivalent-face-in-list-p
    (halfspaces plane face-list)
  (if (consp face-list)
      (or
       (ht013-face-equivalent-p
        halfspaces plane (car face-list))
       (ht013-equivalent-face-in-list-p
        halfspaces plane (cdr face-list)))
    nil))

(defun ht013-no-equivalent-face-in-list-p
    (halfspaces plane face-list)
  (if (consp face-list)
      (and
       (not
        (ht013-face-equivalent-p
         halfspaces plane (car face-list)))
       (ht013-no-equivalent-face-in-list-p
        halfspaces plane (cdr face-list)))
    t))

(defun ht013-face-list-sound-p
    (halfspaces face-list dimension zero)
  (if (consp face-list)
      (and
       (ht013-face-of-dimension-p
        halfspaces (car face-list) dimension zero)
       (ht013-face-list-sound-p
        halfspaces (cdr face-list) dimension zero))
    (equal face-list nil)))

(defun ht013-face-list-distinct-p (halfspaces face-list)
  (if (consp face-list)
      (and
       (ht013-no-equivalent-face-in-list-p
        halfspaces (car face-list) (cdr face-list))
       (ht013-face-list-distinct-p
        halfspaces (cdr face-list)))
    (equal face-list nil)))

(defun-sk ht013-face-list-complete-p
    (halfspaces face-list dimension zero)
  (forall (plane)
    (implies
     (ht013-face-of-dimension-p
      halfspaces plane dimension zero)
     (ht013-equivalent-face-in-list-p
      halfspaces plane face-list))))

(defun ht013-face-enumeration-p
    (halfspaces face-list dimension zero)
  (and
   (true-listp face-list)
   (ht013-face-list-sound-p
    halfspaces face-list dimension zero)
   (ht013-face-list-distinct-p halfspaces face-list)
   (ht013-face-list-complete-p
    halfspaces face-list dimension zero)))

(defun-sk ht013-euler-enumerations-exist-p
    (halfspaces zero)
  (exists (vertices edges facets)
    (and
     (ht013-face-enumeration-p
      halfspaces vertices 0 zero)
     (ht013-face-enumeration-p
      halfspaces edges 1 zero)
     (ht013-face-enumeration-p
      halfspaces facets 2 zero)
     (equal
      (+ (len vertices) (len facets))
      (+ (len edges) 2)))))

(defun-sk hundred-theorems-013-polyhedron-formula-statement
    (zero one)
  (forall (halfspaces)
    (implies
     (and
      (ht013-real-scalar-context-p zero one)
      (ht013-polytope3-p halfspaces zero))
     (ht013-euler-enumerations-exist-p
      halfspaces zero))))

(value-triple :itpeval-statement-checked)
:q
