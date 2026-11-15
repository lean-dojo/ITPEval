;; Statement-only formalization of Babel-formal corpus artifact galois:
;; cancellation and inverse laws for arbitrary fields, and solvability
;; propagation through map-sensitive polynomial maps and splitting-field
;; towers over arbitrary types. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A field structure is represented by a tag together with conservative
;; operations indexed by that tag. Its carrier is an arbitrary predicate,
;; not an enumeration, and every source law and typing condition is explicit.

(defstub galois-field-element-p (field value) t)
(defstub galois-field-zero (field) t)
(defstub galois-field-one (field) t)
(defstub galois-field-add (field x y) t)
(defstub galois-field-mul (field x y) t)
(defstub galois-field-opp (field x) t)
(defstub galois-field-inv (field x) t)

(defun-sk galois-field-laws-p (field)
  (forall (x y z)
    (and
     (implies
      (and
       (galois-field-element-p field x)
       (galois-field-element-p field y))
      (and
       (galois-field-element-p
        field (galois-field-add field x y))
       (galois-field-element-p
        field (galois-field-mul field x y))
       (equal
        (galois-field-add field x y)
        (galois-field-add field y x))
       (equal
        (galois-field-mul field x y)
        (galois-field-mul field y x))))
     (implies
      (galois-field-element-p field x)
      (and
       (galois-field-element-p
        field (galois-field-opp field x))
       (galois-field-element-p
        field (galois-field-inv field x))
       (equal
        (galois-field-add
         field x (galois-field-zero field))
        x)
       (equal
        (galois-field-add
         field (galois-field-opp field x) x)
        (galois-field-zero field))
       (equal
        (galois-field-mul
         field (galois-field-one field) x)
        x)
       (implies
        (not (equal x (galois-field-zero field)))
        (and
         (equal
          (galois-field-mul
           field (galois-field-inv field x) x)
          (galois-field-one field))
         (not
          (equal
           (galois-field-inv field x)
           (galois-field-zero field)))))))
     (implies
      (and
       (galois-field-element-p field x)
       (galois-field-element-p field y)
       (galois-field-element-p field z))
      (and
       (equal
        (galois-field-add
         field (galois-field-add field x y) z)
        (galois-field-add
         field x (galois-field-add field y z)))
       (equal
        (galois-field-mul
         field (galois-field-mul field x y) z)
        (galois-field-mul
         field x (galois-field-mul field y z)))
       (equal
        (galois-field-mul
         field x (galois-field-add field y z))
        (galois-field-add
         field
         (galois-field-mul field x y)
         (galois-field-mul field x z))))))))

(defun galois-field-p (field)
  (and
   (galois-field-element-p
    field (galois-field-zero field))
   (galois-field-element-p
    field (galois-field-one field))
   (not
    (equal
     (galois-field-zero field)
     (galois-field-one field)))
   (galois-field-laws-p field)))

(defun-sk galois-add-cancel-left-statement ()
  (forall (field x y z)
    (implies
     (and
      (galois-field-p field)
      (galois-field-element-p field x)
      (galois-field-element-p field y)
      (galois-field-element-p field z)
      (equal
       (galois-field-add field x y)
       (galois-field-add field x z)))
     (equal y z))))

(defun-sk galois-add-cancel-right-statement ()
  (forall (field x y z)
    (implies
     (and
      (galois-field-p field)
      (galois-field-element-p field x)
      (galois-field-element-p field y)
      (galois-field-element-p field z)
      (equal
       (galois-field-add field y x)
       (galois-field-add field z x)))
     (equal y z))))

(defun-sk galois-mul-cancel-left-statement ()
  (forall (field x y z)
    (implies
     (and
      (galois-field-p field)
      (galois-field-element-p field x)
      (galois-field-element-p field y)
      (galois-field-element-p field z)
      (not (equal x (galois-field-zero field)))
      (equal
       (galois-field-mul field x y)
       (galois-field-mul field x z)))
     (equal y z))))

(defun-sk galois-mul-cancel-right-statement ()
  (forall (field x y z)
    (implies
     (and
      (galois-field-p field)
      (galois-field-element-p field x)
      (galois-field-element-p field y)
      (galois-field-element-p field z)
      (not (equal x (galois-field-zero field)))
      (equal
       (galois-field-mul field y x)
       (galois-field-mul field z x)))
     (equal y z))))

(defun-sk galois-inverse-unique-statement ()
  (forall (field x y)
    (implies
     (and
      (galois-field-p field)
      (galois-field-element-p field x)
      (galois-field-element-p field y)
      (not (equal x (galois-field-zero field)))
      (equal
       (galois-field-mul field x y)
       (galois-field-one field)))
     (equal y (galois-field-inv field x)))))

(defun-sk galois-inverse-involutive-statement ()
  (forall (field x)
    (implies
     (and
      (galois-field-p field)
      (galois-field-element-p field x)
      (not (equal x (galois-field-zero field))))
     (equal
      (galois-field-inv
       field (galois-field-inv field x))
      x))))

;; The tower tag packages the source's polymorphic polynomial family,
;; splitting-field family, algebra maps, Splits predicate, polynomial mapping,
;; Gal family, and IsSolvable predicate. Types, polynomials, and coefficient
;; maps remain arbitrary ACL2 objects guarded by predicates. Map application
;; and composition are explicit, so map_poly and Splits can distinguish maps
;; having the same source and target types.

(defstub galois-type-p (tower type) t)
(defstub galois-type-element-p (tower type value) t)
(defstub galois-polynomial-p (tower coefficient-type polynomial) t)

(defstub galois-coefficient-map-apply (tower map value) t)
(defstub galois-algebra-map (tower source-type target-type) t)
(defstub galois-compose-coefficient-maps
  (tower source-type middle-type target-type first-map second-map)
  t)

(defstub galois-splitting-field
  (tower coefficient-type polynomial)
  t)
(defstub galois-map-poly
  (tower source-type target-type polynomial coefficient-map)
  t)
(defstub galois-splits-p
  (tower source-type target-type polynomial coefficient-map)
  t)
(defstub galois-gal
  (tower coefficient-type polynomial)
  t)
(defstub galois-is-solvable-p (tower group-type) t)

(defun-sk galois-coefficient-map-p
    (tower source-type target-type map)
  (forall (x)
    (implies
     (galois-type-element-p tower source-type x)
     (galois-type-element-p
      tower target-type
      (galois-coefficient-map-apply tower map x)))))

(defun-sk galois-tower-signature-p (tower)
  (forall
    (source-type middle-type target-type polynomial
                 first-map second-map x)
    (and
     (implies
      (and
       (galois-type-p tower source-type)
       (galois-polynomial-p
        tower source-type polynomial))
      (and
       (galois-type-p
        tower
        (galois-splitting-field
         tower source-type polynomial))
       (galois-type-p
        tower
        (galois-gal tower source-type polynomial))))
     (implies
      (and
       (galois-type-p tower source-type)
       (galois-type-p tower target-type))
      (galois-coefficient-map-p
       tower source-type target-type
       (galois-algebra-map
        tower source-type target-type)))
     (implies
      (and
       (galois-type-p tower source-type)
       (galois-type-p tower target-type)
       (galois-polynomial-p
        tower source-type polynomial)
       (galois-coefficient-map-p
        tower source-type target-type first-map))
      (galois-polynomial-p
       tower target-type
       (galois-map-poly
        tower source-type target-type
        polynomial first-map)))
     (implies
      (and
       (galois-type-p tower source-type)
       (galois-type-p tower middle-type)
       (galois-type-p tower target-type)
       (galois-coefficient-map-p
        tower source-type middle-type first-map)
       (galois-coefficient-map-p
        tower middle-type target-type second-map))
      (and
       (galois-coefficient-map-p
        tower source-type target-type
        (galois-compose-coefficient-maps
         tower source-type middle-type target-type
         first-map second-map))
       (implies
        (galois-type-element-p tower source-type x)
        (equal
         (galois-coefficient-map-apply
          tower
          (galois-compose-coefficient-maps
           tower source-type middle-type target-type
           first-map second-map)
          x)
         (galois-coefficient-map-apply
          tower second-map
          (galois-coefficient-map-apply
           tower first-map x)))))))))

(defun galois-polynomial-solvable-p
    (tower coefficient-type polynomial)
  (galois-is-solvable-p
   tower
   (galois-gal tower coefficient-type polynomial)))

(defun-sk galois-map-poly-comp-assumption-p (tower)
  (forall
    (source-type middle-type target-type polynomial
                 first-map second-map)
    (implies
     (and
      (galois-type-p tower source-type)
      (galois-type-p tower middle-type)
      (galois-type-p tower target-type)
      (galois-polynomial-p
       tower source-type polynomial)
      (galois-coefficient-map-p
       tower source-type middle-type first-map)
      (galois-coefficient-map-p
       tower middle-type target-type second-map))
     (equal
      (galois-map-poly
       tower middle-type target-type
       (galois-map-poly
        tower source-type middle-type polynomial first-map)
       second-map)
      (galois-map-poly
       tower source-type target-type polynomial
       (galois-compose-coefficient-maps
        tower source-type middle-type target-type
        first-map second-map))))))

(defun-sk galois-scalar-tower-assumption-p (tower)
  (forall (source-type target-type p q)
    (implies
     (and
      (galois-type-p tower source-type)
      (galois-type-p tower target-type)
      (galois-polynomial-p tower source-type p)
      (galois-polynomial-p tower source-type q)
      (galois-polynomial-solvable-p
       tower source-type p)
      (galois-polynomial-solvable-p
       tower target-type
       (galois-map-poly
        tower source-type target-type q
        (galois-algebra-map
         tower source-type target-type))))
     (galois-polynomial-solvable-p
      tower source-type q))))

(defun-sk galois-map-solvable-assumption-p (tower)
  (forall (source-type target-type polynomial)
    (implies
     (and
      (galois-type-p tower source-type)
      (galois-type-p tower target-type)
      (galois-polynomial-p
       tower source-type polynomial)
      (galois-polynomial-solvable-p
       tower source-type polynomial))
     (galois-polynomial-solvable-p
      tower target-type
      (galois-map-poly
       tower source-type target-type polynomial
       (galois-algebra-map
        tower source-type target-type))))))

(defun-sk galois-splits-solvable-assumption-p (tower)
  (forall
    (source-type target-type polynomial coefficient-map)
    (implies
     (and
      (galois-type-p tower source-type)
      (galois-type-p tower target-type)
      (galois-polynomial-p
       tower source-type polynomial)
      (galois-coefficient-map-p
       tower source-type target-type coefficient-map)
      (galois-splits-p
       tower source-type target-type
       polynomial coefficient-map))
     (galois-polynomial-solvable-p
      tower source-type polynomial))))

(defun galois-tower-context-p (tower)
  (and
   (galois-tower-signature-p tower)
   (galois-map-poly-comp-assumption-p tower)
   (galois-scalar-tower-assumption-p tower)
   (galois-map-solvable-assumption-p tower)
   (galois-splits-solvable-assumption-p tower)))

(defun-sk galois-solvable-tower-statement ()
  (forall (tower source-type p q)
    (let ((split-p
           (galois-splitting-field
            tower source-type p)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-polynomial-solvable-p
         tower source-type p)
        (galois-polynomial-solvable-p
         tower split-p
         (galois-map-poly
          tower source-type split-p q
          (galois-algebra-map
           tower source-type split-p))))
       (galois-polynomial-solvable-p
        tower source-type q)))))

(defun-sk galois-solvable-double-tower-statement ()
  (forall (tower source-type p q r)
    (let ((split-p
           (galois-splitting-field
            tower source-type p))
          (split-q
           (galois-splitting-field
            tower source-type q)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-polynomial-p tower source-type r)
        (galois-polynomial-solvable-p
         tower source-type p)
        (galois-polynomial-solvable-p
         tower split-p
         (galois-map-poly
          tower source-type split-p q
          (galois-algebra-map
           tower source-type split-p)))
        (galois-polynomial-solvable-p
         tower split-q
         (galois-map-poly
          tower source-type split-q r
          (galois-algebra-map
           tower source-type split-q))))
       (galois-polynomial-solvable-p
        tower source-type r)))))

(defun-sk galois-solvable-triple-tower-statement ()
  (forall (tower source-type p q r s)
    (let ((split-p
           (galois-splitting-field
            tower source-type p))
          (split-q
           (galois-splitting-field
            tower source-type q))
          (split-r
           (galois-splitting-field
            tower source-type r)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-polynomial-p tower source-type r)
        (galois-polynomial-p tower source-type s)
        (galois-polynomial-solvable-p
         tower source-type p)
        (galois-polynomial-solvable-p
         tower split-p
         (galois-map-poly
          tower source-type split-p q
          (galois-algebra-map
           tower source-type split-p)))
        (galois-polynomial-solvable-p
         tower split-q
         (galois-map-poly
          tower source-type split-q r
          (galois-algebra-map
           tower source-type split-q)))
        (galois-polynomial-solvable-p
         tower split-r
         (galois-map-poly
          tower source-type split-r s
          (galois-algebra-map
           tower source-type split-r))))
       (galois-polynomial-solvable-p
        tower source-type s)))))

(defun-sk galois-solvable-quadruple-tower-statement ()
  (forall (tower source-type p q r s u)
    (let ((split-p
           (galois-splitting-field
            tower source-type p))
          (split-q
           (galois-splitting-field
            tower source-type q))
          (split-r
           (galois-splitting-field
            tower source-type r))
          (split-s
           (galois-splitting-field
            tower source-type s)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-polynomial-p tower source-type r)
        (galois-polynomial-p tower source-type s)
        (galois-polynomial-p tower source-type u)
        (galois-polynomial-solvable-p
         tower source-type p)
        (galois-polynomial-solvable-p
         tower split-p
         (galois-map-poly
          tower source-type split-p q
          (galois-algebra-map
           tower source-type split-p)))
        (galois-polynomial-solvable-p
         tower split-q
         (galois-map-poly
          tower source-type split-q r
          (galois-algebra-map
           tower source-type split-q)))
        (galois-polynomial-solvable-p
         tower split-r
         (galois-map-poly
          tower source-type split-r s
          (galois-algebra-map
           tower source-type split-r)))
        (galois-polynomial-solvable-p
         tower split-s
         (galois-map-poly
          tower source-type split-s u
          (galois-algebra-map
           tower source-type split-s))))
       (galois-polynomial-solvable-p
        tower source-type u)))))

(defun-sk galois-solvable-map-poly-statement ()
  (forall (tower source-type target-type polynomial)
    (implies
     (and
      (galois-tower-context-p tower)
      (galois-type-p tower source-type)
      (galois-type-p tower target-type)
      (galois-polynomial-p
       tower source-type polynomial)
      (galois-polynomial-solvable-p
       tower source-type polynomial))
     (galois-polynomial-solvable-p
      tower target-type
      (galois-map-poly
       tower source-type target-type polynomial
       (galois-algebra-map
        tower source-type target-type))))))

(defun-sk galois-solvable-of-split-statement ()
  (forall (tower source-type polynomial)
    (let ((split-type
           (galois-splitting-field
            tower source-type polynomial)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p
         tower source-type polynomial)
        (galois-splits-p
         tower source-type split-type polynomial
         (galois-algebra-map
          tower source-type split-type)))
       (galois-polynomial-solvable-p
        tower source-type polynomial)))))

(defun-sk galois-solvable-split-tower-statement ()
  (forall (tower source-type p q)
    (let ((split-p
           (galois-splitting-field
            tower source-type p)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-splits-p
         tower source-type split-p q
         (galois-algebra-map
          tower source-type split-p)))
       (galois-polynomial-solvable-p
        tower source-type q)))))

(defun-sk galois-solvable-two-step-map-statement ()
  (forall
    (tower source-type middle-type target-type polynomial)
    (let* ((first-map
            (galois-algebra-map
             tower source-type middle-type))
           (second-map
            (galois-algebra-map
             tower middle-type target-type))
           (first-polynomial
            (galois-map-poly
             tower source-type middle-type
             polynomial first-map)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-type-p tower middle-type)
        (galois-type-p tower target-type)
        (galois-polynomial-p
         tower source-type polynomial)
        (galois-polynomial-solvable-p
         tower source-type polynomial))
       (galois-polynomial-solvable-p
        tower target-type
        (galois-map-poly
         tower middle-type target-type
         first-polynomial second-map))))))

(defun-sk galois-solvable-three-step-map-statement ()
  (forall
    (tower source-type first-type second-type target-type polynomial)
    (let* ((first-map
            (galois-algebra-map
             tower source-type first-type))
           (second-map
            (galois-algebra-map
             tower first-type second-type))
           (third-map
            (galois-algebra-map
             tower second-type target-type))
           (first-polynomial
            (galois-map-poly
             tower source-type first-type
             polynomial first-map))
           (second-polynomial
            (galois-map-poly
             tower first-type second-type
             first-polynomial second-map)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-type-p tower first-type)
        (galois-type-p tower second-type)
        (galois-type-p tower target-type)
        (galois-polynomial-p
         tower source-type polynomial)
        (galois-polynomial-solvable-p
         tower source-type polynomial))
       (galois-polynomial-solvable-p
        tower target-type
        (galois-map-poly
         tower second-type target-type
         second-polynomial third-map))))))

(defun-sk galois-solvable-map-poly-comp-statement ()
  (forall
    (tower source-type middle-type target-type polynomial)
    (let* ((first-map
            (galois-algebra-map
             tower source-type middle-type))
           (second-map
            (galois-algebra-map
             tower middle-type target-type))
           (first-polynomial
            (galois-map-poly
             tower source-type middle-type
             polynomial first-map)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-type-p tower middle-type)
        (galois-type-p tower target-type)
        (galois-polynomial-p
         tower source-type polynomial)
        (galois-polynomial-solvable-p
         tower source-type polynomial))
       (galois-polynomial-solvable-p
        tower target-type
        (galois-map-poly
         tower middle-type target-type
         first-polynomial second-map))))))

(defun-sk galois-solvable-mutual-split-statement ()
  (forall (tower source-type p q)
    (let ((split-p
           (galois-splitting-field
            tower source-type p))
          (split-q
           (galois-splitting-field
            tower source-type q)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-splits-p
         tower source-type split-q p
         (galois-algebra-map
          tower source-type split-q))
        (galois-splits-p
         tower source-type split-p q
         (galois-algebra-map
          tower source-type split-p)))
       (and
        (galois-polynomial-solvable-p
         tower source-type p)
        (galois-polynomial-solvable-p
         tower source-type q))))))

(defun-sk galois-solvable-tower-split-statement ()
  (forall (tower source-type p q r)
    (let ((split-p
           (galois-splitting-field
            tower source-type p))
          (split-q
           (galois-splitting-field
            tower source-type q)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-polynomial-p tower source-type p)
        (galois-polynomial-p tower source-type q)
        (galois-polynomial-p tower source-type r)
        (galois-splits-p
         tower source-type split-p q
         (galois-algebra-map
          tower source-type split-p))
        (galois-polynomial-solvable-p
         tower split-q
         (galois-map-poly
          tower source-type split-q r
          (galois-algebra-map
           tower source-type split-q))))
       (galois-polynomial-solvable-p
        tower source-type r)))))

(defun-sk galois-solvable-map-after-split-statement ()
  (forall (tower source-type target-type polynomial)
    (let ((split-type
           (galois-splitting-field
            tower source-type polynomial)))
      (implies
       (and
        (galois-tower-context-p tower)
        (galois-type-p tower source-type)
        (galois-type-p tower target-type)
        (galois-polynomial-p
         tower source-type polynomial)
        (galois-splits-p
         tower source-type split-type polynomial
         (galois-algebra-map
          tower source-type split-type)))
       (galois-polynomial-solvable-p
        tower target-type
        (galois-map-poly
         tower source-type target-type polynomial
         (galois-algebra-map
          tower source-type target-type)))))))

(defun babel-formal-galois-statement ()
  (and
   (galois-add-cancel-left-statement)
   (galois-add-cancel-right-statement)
   (galois-mul-cancel-left-statement)
   (galois-mul-cancel-right-statement)
   (galois-inverse-unique-statement)
   (galois-inverse-involutive-statement)
   (galois-solvable-tower-statement)
   (galois-solvable-double-tower-statement)
   (galois-solvable-triple-tower-statement)
   (galois-solvable-quadruple-tower-statement)
   (galois-solvable-map-poly-statement)
   (galois-solvable-of-split-statement)
   (galois-solvable-split-tower-statement)
   (galois-solvable-two-step-map-statement)
   (galois-solvable-three-step-map-statement)
   (galois-solvable-map-poly-comp-statement)
   (galois-solvable-mutual-split-statement)
   (galois-solvable-tower-split-statement)
   (galois-solvable-map-after-split-statement)))

(value-triple :itpeval-statement-checked)
:q
