;; Statement-only formalization of Hundred Theorems artifact 050,
;; "The Number of Platonic Solids." A full-dimensional convex polytope in
;; three-dimensional real space with m edges on each facet and n incident
;; edges at each vertex exists exactly for the five Platonic pairs. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; ACL2's built-in numbers are not the real numbers, so the scalar structure
;; is an explicit real-closed ordered field. Real closedness is the
;; first-order algebraic theory of the reals needed by this statement.

(defstub ht050-carrier (x) t)
(defstub ht050-add-op (x y) t)
(defstub ht050-multiply-op (x y) t)
(defstub ht050-negate-op (x) t)
(defstub ht050-inverse-op (x) t)
(defstub ht050-less-op (x y) t)

(defun ht050-member-p (x)
  (if (ht050-carrier x) t nil))

(defun ht050-add (x y)
  (ht050-add-op x y))

(defun ht050-multiply (x y)
  (ht050-multiply-op x y))

(defun ht050-negate (x)
  (ht050-negate-op x))

(defun ht050-inverse (x)
  (ht050-inverse-op x))

(defun ht050-subtract (x y)
  (ht050-add x (ht050-negate y)))

(defun ht050-less (x y)
  (if (ht050-less-op x y) t nil))

(defun ht050-less-or-equal (x y)
  (or (equal x y)
      (ht050-less x y)))

(defun ht050-square (x)
  (ht050-multiply x x))

(defun-sk ht050-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht050-member-p x)
      (ht050-member-p y)
      (ht050-member-p z))
     (and
      (ht050-member-p (ht050-add x y))
      (ht050-member-p (ht050-multiply x y))
      (ht050-member-p (ht050-negate x))
      (ht050-member-p (ht050-inverse x))
      (equal (ht050-add (ht050-add x y) z)
             (ht050-add x (ht050-add y z)))
      (equal (ht050-add x y)
             (ht050-add y x))
      (equal (ht050-add x zero) x)
      (equal (ht050-add x (ht050-negate x)) zero)
      (equal (ht050-multiply (ht050-multiply x y) z)
             (ht050-multiply x (ht050-multiply y z)))
      (equal (ht050-multiply x y)
             (ht050-multiply y x))
      (equal (ht050-multiply x one) x)
      (equal
       (ht050-multiply x (ht050-add y z))
       (ht050-add
        (ht050-multiply x y)
        (ht050-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht050-multiply x (ht050-inverse x))
        one))))))

(defun-sk ht050-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht050-member-p x)
      (ht050-member-p y)
      (ht050-member-p z))
     (and
      (not (ht050-less x x))
      (or
       (equal x y)
       (ht050-less x y)
       (ht050-less y x))
      (implies
       (and
        (ht050-less x y)
        (ht050-less y z))
       (ht050-less x z))
      (implies
       (ht050-less x y)
       (ht050-less
        (ht050-add x z)
        (ht050-add y z)))
      (implies
       (and
        (ht050-less zero x)
        (ht050-less zero y))
       (ht050-less zero (ht050-multiply x y)))))))

(defun ht050-field-list-p (values)
  (if (consp values)
      (and
       (ht050-member-p (car values))
       (ht050-field-list-p (cdr values)))
    (equal values nil)))

(defun ht050-polynomial-value (coefficients x zero)
  (if (consp coefficients)
      (ht050-add
       (car coefficients)
       (ht050-multiply
        x
        (ht050-polynomial-value (cdr coefficients) x zero)))
    zero))

(defun ht050-odd-degree-polynomial-p (coefficients zero)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht050-field-list-p coefficients)
   (evenp (len coefficients))
   (not (equal (car (last coefficients)) zero))))

(defun-sk ht050-has-square-root-p (x zero)
  (exists (root)
    (and
     (ht050-member-p root)
     (equal (ht050-square root) x))))

(defun-sk ht050-has-polynomial-root-p (coefficients zero)
  (exists (root)
    (and
     (ht050-member-p root)
     (equal
      (ht050-polynomial-value coefficients root zero)
      zero))))

(defun-sk ht050-real-closure-laws-p (zero)
  (forall (x coefficients)
    (and
     (implies
      (and
       (ht050-member-p x)
       (not (ht050-less x zero)))
      (ht050-has-square-root-p x zero))
     (implies
      (ht050-odd-degree-polynomial-p coefficients zero)
      (ht050-has-polynomial-root-p coefficients zero)))))

(defun ht050-real-scalar-context-p (zero one)
  (and
   (ht050-member-p zero)
   (ht050-member-p one)
   (not (equal zero one))
   (ht050-less zero one)
   (ht050-field-laws-p zero one)
   (ht050-order-laws-p zero)
   (ht050-real-closure-laws-p zero)))

;; A point is the proper list (x y z), and a plane is the proper list
;; (a b c d), denoting a*x + b*y + c*z = d. A polytope is represented by a
;; finite list of planes whose corresponding closed half-spaces are
;; intersected.

(defun ht050-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (ht050-member-p (nth 0 point))
   (ht050-member-p (nth 1 point))
   (ht050-member-p (nth 2 point))))

(defun ht050-point-x (point)
  (nth 0 point))

(defun ht050-point-y (point)
  (nth 1 point))

(defun ht050-point-z (point)
  (nth 2 point))

(defun ht050-plane-p (plane zero)
  (and
   (true-listp plane)
   (equal (len plane) 4)
   (ht050-member-p (nth 0 plane))
   (ht050-member-p (nth 1 plane))
   (ht050-member-p (nth 2 plane))
   (ht050-member-p (nth 3 plane))
   (not
    (and
     (equal (nth 0 plane) zero)
     (equal (nth 1 plane) zero)
     (equal (nth 2 plane) zero)))))

(defun ht050-plane-value (plane point)
  (ht050-add
   (ht050-add
    (ht050-multiply (nth 0 plane) (ht050-point-x point))
    (ht050-multiply (nth 1 plane) (ht050-point-y point)))
   (ht050-multiply (nth 2 plane) (ht050-point-z point))))

(defun ht050-plane-bound (plane)
  (nth 3 plane))

(defun ht050-halfspace-list-p (halfspaces zero)
  (if (consp halfspaces)
      (and
       (ht050-plane-p (car halfspaces) zero)
       (ht050-halfspace-list-p (cdr halfspaces) zero))
    (equal halfspaces nil)))

(defun ht050-point-in-polytope-p (point halfspaces)
  (and
   (ht050-point-p point)
   (if (consp halfspaces)
       (and
        (ht050-less-or-equal
         (ht050-plane-value (car halfspaces) point)
         (ht050-plane-bound (car halfspaces)))
        (ht050-point-in-polytope-p point (cdr halfspaces)))
     (equal halfspaces nil))))

(defun ht050-coordinate-bounded-p (coordinate bound)
  (and
   (ht050-less-or-equal (ht050-negate bound) coordinate)
   (ht050-less-or-equal coordinate bound)))

(defun-sk ht050-bound-works-p (halfspaces bound)
  (forall (point)
    (implies
     (ht050-point-in-polytope-p point halfspaces)
     (and
      (ht050-coordinate-bounded-p (ht050-point-x point) bound)
      (ht050-coordinate-bounded-p (ht050-point-y point) bound)
      (ht050-coordinate-bounded-p (ht050-point-z point) bound)))))

(defun-sk ht050-bounded-p (halfspaces zero)
  (exists (bound)
    (and
     (ht050-member-p bound)
     (ht050-less zero bound)
     (ht050-bound-works-p halfspaces bound))))

(defun ht050-distance-squared (first second)
  (let ((dx (ht050-subtract
             (ht050-point-x first)
             (ht050-point-x second)))
        (dy (ht050-subtract
             (ht050-point-y first)
             (ht050-point-y second)))
        (dz (ht050-subtract
             (ht050-point-z first)
             (ht050-point-z second))))
    (ht050-add
     (ht050-add (ht050-square dx) (ht050-square dy))
     (ht050-square dz))))

(defun-sk ht050-open-ball-contained-p (halfspaces center radius)
  (forall (point)
    (implies
     (and
      (ht050-point-p point)
      (ht050-less
       (ht050-distance-squared point center)
       (ht050-square radius)))
     (ht050-point-in-polytope-p point halfspaces))))

(defun-sk ht050-full-dimensional-p (halfspaces zero)
  (exists (center radius)
    (and
     (ht050-point-p center)
     (ht050-member-p radius)
     (ht050-less zero radius)
     (ht050-open-ball-contained-p halfspaces center radius))))

(defun ht050-polytope3-p (halfspaces zero)
  (and
   (true-listp halfspaces)
   (ht050-halfspace-list-p halfspaces zero)
   (ht050-bounded-p halfspaces zero)
   (ht050-full-dimensional-p halfspaces zero)))

;; Every face of a polytope is exposed. A plane descriptor represents the
;; nonempty face where a supporting inequality is tight.

(defun-sk ht050-supporting-plane-p (halfspaces plane)
  (forall (point)
    (implies
     (ht050-point-in-polytope-p point halfspaces)
     (ht050-less-or-equal
      (ht050-plane-value plane point)
      (ht050-plane-bound plane)))))

(defun ht050-point-in-face-p (point halfspaces plane)
  (and
   (ht050-point-in-polytope-p point halfspaces)
   (equal
    (ht050-plane-value plane point)
    (ht050-plane-bound plane))))

(defun-sk ht050-face-equivalent-p
    (halfspaces first-plane second-plane)
  (forall (point)
    (equal
     (ht050-point-in-face-p point halfspaces first-plane)
     (ht050-point-in-face-p point halfspaces second-plane))))

;; Affine dimensions zero, one, and two are expressed intrinsically. The
;; quantified scalars in on-line and on-plane range over the field carrier.

(defun-sk ht050-on-line-p (point first second)
  (exists (parameter)
    (and
     (ht050-member-p parameter)
     (equal
      (ht050-point-x point)
      (ht050-add
       (ht050-point-x first)
       (ht050-multiply
        parameter
        (ht050-subtract
         (ht050-point-x second)
         (ht050-point-x first)))))
     (equal
      (ht050-point-y point)
      (ht050-add
       (ht050-point-y first)
       (ht050-multiply
        parameter
        (ht050-subtract
         (ht050-point-y second)
         (ht050-point-y first)))))
     (equal
      (ht050-point-z point)
      (ht050-add
       (ht050-point-z first)
       (ht050-multiply
        parameter
        (ht050-subtract
         (ht050-point-z second)
         (ht050-point-z first))))))))

(defun ht050-cross-x (first second third)
  (ht050-subtract
   (ht050-multiply
    (ht050-subtract (ht050-point-y second) (ht050-point-y first))
    (ht050-subtract (ht050-point-z third) (ht050-point-z first)))
   (ht050-multiply
    (ht050-subtract (ht050-point-z second) (ht050-point-z first))
    (ht050-subtract (ht050-point-y third) (ht050-point-y first)))))

(defun ht050-cross-y (first second third)
  (ht050-subtract
   (ht050-multiply
    (ht050-subtract (ht050-point-z second) (ht050-point-z first))
    (ht050-subtract (ht050-point-x third) (ht050-point-x first)))
   (ht050-multiply
    (ht050-subtract (ht050-point-x second) (ht050-point-x first))
    (ht050-subtract (ht050-point-z third) (ht050-point-z first)))))

(defun ht050-cross-z (first second third)
  (ht050-subtract
   (ht050-multiply
    (ht050-subtract (ht050-point-x second) (ht050-point-x first))
    (ht050-subtract (ht050-point-y third) (ht050-point-y first)))
   (ht050-multiply
    (ht050-subtract (ht050-point-y second) (ht050-point-y first))
    (ht050-subtract (ht050-point-x third) (ht050-point-x first)))))

(defun ht050-affinely-independent-three-p
    (first second third zero)
  (or
   (not (equal (ht050-cross-x first second third) zero))
   (not (equal (ht050-cross-y first second third) zero))
   (not (equal (ht050-cross-z first second third) zero))))

(defun-sk ht050-on-plane-p (point first second third)
  (exists (first-parameter second-parameter)
    (and
     (ht050-member-p first-parameter)
     (ht050-member-p second-parameter)
     (equal
      (ht050-point-x point)
      (ht050-add
       (ht050-add
        (ht050-point-x first)
        (ht050-multiply
         first-parameter
         (ht050-subtract
          (ht050-point-x second)
          (ht050-point-x first))))
       (ht050-multiply
        second-parameter
        (ht050-subtract
         (ht050-point-x third)
         (ht050-point-x first)))))
     (equal
      (ht050-point-y point)
      (ht050-add
       (ht050-add
        (ht050-point-y first)
        (ht050-multiply
         first-parameter
         (ht050-subtract
          (ht050-point-y second)
          (ht050-point-y first))))
       (ht050-multiply
        second-parameter
        (ht050-subtract
         (ht050-point-y third)
         (ht050-point-y first)))))
     (equal
      (ht050-point-z point)
      (ht050-add
       (ht050-add
        (ht050-point-z first)
        (ht050-multiply
         first-parameter
         (ht050-subtract
          (ht050-point-z second)
          (ht050-point-z first))))
       (ht050-multiply
        second-parameter
        (ht050-subtract
         (ht050-point-z third)
         (ht050-point-z first))))))))

(defun-sk ht050-face-is-singleton-p
    (halfspaces plane point)
  (forall (other)
    (implies
     (ht050-point-in-face-p other halfspaces plane)
     (equal other point))))

(defun-sk ht050-face-dimension-zero-p
    (halfspaces plane)
  (exists (point)
    (and
     (ht050-point-in-face-p point halfspaces plane)
     (ht050-face-is-singleton-p halfspaces plane point))))

(defun-sk ht050-face-contained-in-line-p
    (halfspaces plane first second)
  (forall (point)
    (implies
     (ht050-point-in-face-p point halfspaces plane)
     (ht050-on-line-p point first second))))

(defun-sk ht050-face-dimension-one-p
    (halfspaces plane)
  (exists (first second)
    (and
     (ht050-point-in-face-p first halfspaces plane)
     (ht050-point-in-face-p second halfspaces plane)
     (not (equal first second))
     (ht050-face-contained-in-line-p
      halfspaces plane first second))))

(defun-sk ht050-face-contained-in-plane-p
    (halfspaces plane first second third)
  (forall (point)
    (implies
     (ht050-point-in-face-p point halfspaces plane)
     (ht050-on-plane-p point first second third))))

(defun-sk ht050-face-dimension-two-p
    (halfspaces plane zero)
  (exists (first second third)
    (and
     (ht050-point-in-face-p first halfspaces plane)
     (ht050-point-in-face-p second halfspaces plane)
     (ht050-point-in-face-p third halfspaces plane)
     (ht050-affinely-independent-three-p
      first second third zero)
     (ht050-face-contained-in-plane-p
      halfspaces plane first second third))))

(defun ht050-face-of-dimension-p
    (halfspaces plane dimension zero)
  (and
   (ht050-plane-p plane zero)
   (ht050-supporting-plane-p halfspaces plane)
   (cond
    ((equal dimension 0)
     (ht050-face-dimension-zero-p halfspaces plane))
    ((equal dimension 1)
     (ht050-face-dimension-one-p halfspaces plane))
    ((equal dimension 2)
     (ht050-face-dimension-two-p halfspaces plane zero))
    (t nil))))

;; Face incidence is inclusion between the exposed subsets represented by two
;; supporting-plane descriptors.

(defun-sk ht050-face-subset-p
    (halfspaces lower-plane upper-plane)
  (forall (point)
    (implies
     (ht050-point-in-face-p point halfspaces lower-plane)
     (ht050-point-in-face-p point halfspaces upper-plane))))

(defun ht050-edge-incident-to-face-p
    (halfspaces edge-plane face-plane face-dimension zero)
  (and
   (ht050-face-of-dimension-p
    halfspaces edge-plane 1 zero)
   (ht050-face-of-dimension-p
    halfspaces face-plane face-dimension zero)
   (cond
    ((equal face-dimension 2)
     (ht050-face-subset-p
      halfspaces edge-plane face-plane))
    ((equal face-dimension 0)
     (ht050-face-subset-p
      halfspaces face-plane edge-plane))
    (t nil))))

;; A finite list gives the incident edges of one facet or vertex when every
;; descriptor is sound, no two descriptors denote the same edge, and every
;; incident edge is extensionally represented in the list.

(defun ht050-equivalent-face-in-list-p
    (halfspaces plane face-list)
  (if (consp face-list)
      (or
       (ht050-face-equivalent-p
        halfspaces plane (car face-list))
       (ht050-equivalent-face-in-list-p
        halfspaces plane (cdr face-list)))
    nil))

(defun ht050-no-equivalent-face-in-list-p
    (halfspaces plane face-list)
  (if (consp face-list)
      (and
       (not
        (ht050-face-equivalent-p
         halfspaces plane (car face-list)))
       (ht050-no-equivalent-face-in-list-p
        halfspaces plane (cdr face-list)))
    t))

(defun ht050-incident-edge-list-sound-p
    (halfspaces edge-list face-plane face-dimension zero)
  (if (consp edge-list)
      (and
       (ht050-edge-incident-to-face-p
        halfspaces
        (car edge-list)
        face-plane
        face-dimension
        zero)
       (ht050-incident-edge-list-sound-p
        halfspaces
        (cdr edge-list)
        face-plane
        face-dimension
        zero))
    (equal edge-list nil)))

(defun ht050-face-list-distinct-p (halfspaces face-list)
  (if (consp face-list)
      (and
       (ht050-no-equivalent-face-in-list-p
        halfspaces (car face-list) (cdr face-list))
       (ht050-face-list-distinct-p
        halfspaces (cdr face-list)))
    (equal face-list nil)))

(defun-sk ht050-incident-edge-list-complete-p
    (halfspaces edge-list face-plane face-dimension zero)
  (forall (edge-plane)
    (implies
     (ht050-edge-incident-to-face-p
      halfspaces
      edge-plane
      face-plane
      face-dimension
      zero)
     (ht050-equivalent-face-in-list-p
      halfspaces edge-plane edge-list))))

(defun ht050-incident-edge-enumeration-p
    (halfspaces edge-list face-plane face-dimension zero)
  (and
   (true-listp edge-list)
   (ht050-incident-edge-list-sound-p
    halfspaces edge-list face-plane face-dimension zero)
   (ht050-face-list-distinct-p halfspaces edge-list)
   (ht050-incident-edge-list-complete-p
    halfspaces edge-list face-plane face-dimension zero)))

(defun-sk ht050-face-has-edge-count-p
    (halfspaces face-plane face-dimension count zero)
  (exists (edge-list)
    (and
     (ht050-incident-edge-enumeration-p
      halfspaces edge-list face-plane face-dimension zero)
     (equal (len edge-list) count))))

(defun-sk ht050-all-faces-have-edge-count-p
    (halfspaces face-dimension count zero)
  (forall (face-plane)
    (implies
     (ht050-face-of-dimension-p
      halfspaces face-plane face-dimension zero)
     (ht050-face-has-edge-count-p
      halfspaces face-plane face-dimension count zero))))

(defun-sk ht050-uniform-polytope-exists-p
    (face-size vertex-degree zero)
  (exists (halfspaces)
    (and
     (ht050-polytope3-p halfspaces zero)
     (ht050-all-faces-have-edge-count-p
      halfspaces 2 face-size zero)
     (ht050-all-faces-have-edge-count-p
      halfspaces 0 vertex-degree zero))))

(defun ht050-platonic-pair-p (face-size vertex-degree)
  (or
   (and (equal face-size 3)
        (equal vertex-degree 3))
   (and (equal face-size 4)
        (equal vertex-degree 3))
   (and (equal face-size 3)
        (equal vertex-degree 4))
   (and (equal face-size 5)
        (equal vertex-degree 3))
   (and (equal face-size 3)
        (equal vertex-degree 5))))

(defun-sk hundred-theorems-050-the-number-of-platonic-solids-statement
    (zero one)
  (forall (m n)
    (implies
     (and
      (ht050-real-scalar-context-p zero one)
      (natp m)
      (natp n))
     (equal
      (ht050-uniform-polytope-exists-p m n zero)
      (ht050-platonic-pair-p m n)))))

(value-triple :itpeval-statement-checked)
:q
