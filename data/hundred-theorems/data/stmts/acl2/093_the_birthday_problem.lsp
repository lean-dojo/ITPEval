;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__093, "The Birthday Problem": among all functions
;; assigning 365 possible birthdays to 23 people, more than half have a
;; collision, while for 22 people fewer than half have a collision. This file
;; contains no proof.

(in-package "ACL2")

;; A function on a finite person carrier is represented by its image list in
;; carrier order. For duplicate-free carriers, HT093-FUNCTION-IMAGES enumerates
;; every function to the birthday carrier exactly once, so this representation
;; is bijective with the finite function spaces in the source statements.
(defun ht093-prepend-to-each (value image-lists)
  (if (consp image-lists)
      (cons (cons value (car image-lists))
            (ht093-prepend-to-each value (cdr image-lists)))
    nil))

(defun ht093-extend-by-each-image (birthday-carrier image-lists)
  (if (consp birthday-carrier)
      (append
       (ht093-prepend-to-each (car birthday-carrier) image-lists)
       (ht093-extend-by-each-image
        (cdr birthday-carrier) image-lists))
    nil))

(defun ht093-function-images (person-carrier birthday-carrier)
  (if (consp person-carrier)
      (ht093-extend-by-each-image
       birthday-carrier
       (ht093-function-images
        (cdr person-carrier) birthday-carrier))
    (list nil)))

(defun ht093-contains-equal-p (value values)
  (if (consp values)
      (or (equal value (car values))
          (ht093-contains-equal-p value (cdr values)))
    nil))

(defun ht093-collision-p (image-list)
  (if (consp image-list)
      (or (ht093-contains-equal-p (car image-list) (cdr image-list))
          (ht093-collision-p (cdr image-list)))
    nil))

(defun ht093-count-collisions (image-lists)
  (if (consp image-lists)
      (+ (if (ht093-collision-p (car image-lists)) 1 0)
         (ht093-count-collisions (cdr image-lists)))
    0))

(defun hundred-theorems-093-the-birthday-problem-statement
    (people-23 people-22 birthdays)
  (implies
   (and
    (true-listp people-23)
    (no-duplicatesp-equal people-23)
    (equal (len people-23) 23)
    (true-listp people-22)
    (no-duplicatesp-equal people-22)
    (equal (len people-22) 22)
    (true-listp birthdays)
    (no-duplicatesp-equal birthdays)
    (equal (len birthdays) 365))
   (let* ((functions-23
           (ht093-function-images people-23 birthdays))
          (functions-22
           (ht093-function-images people-22 birthdays)))
     (and
      (> (* 2 (ht093-count-collisions functions-23))
         (len functions-23))
      (< (* 2 (ht093-count-collisions functions-22))
         (len functions-22))))))

(value-triple :itpeval-statement-checked)
:q
