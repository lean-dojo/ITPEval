;; Statement-only formalization of Babel-formal artifact group: arbitrary
;; groups and group actions, elementary cancellation and inverse laws, and
;; orbit and stabilizer properties. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic interfaces represent arbitrary carrier predicates,
;; group operations, and actions. Structure tags distinguish instances but do
;; not enumerate or otherwise restrict either carrier.

(defstub babel-group-element-p (group value) t)
(defstub babel-space-element-p (space value) t)
(defstub babel-group-one (group) t)
(defstub babel-group-mul (group left right) t)
(defstub babel-group-inv (group value) t)
(defstub babel-group-act (action group-element point) t)

(defun-sk babel-group-laws-p (group)
  (forall (a b c)
    (and
     (implies
      (babel-group-element-p group a)
      (and
       (babel-group-element-p
        group (babel-group-inv group a))
       (equal
        (babel-group-mul
         group a (babel-group-one group))
        a)
       (equal
        (babel-group-mul
         group (babel-group-one group) a)
        a)
       (equal
        (babel-group-mul
         group (babel-group-inv group a) a)
        (babel-group-one group))
       (equal
        (babel-group-mul
         group a (babel-group-inv group a))
        (babel-group-one group))))
     (implies
      (and
       (babel-group-element-p group a)
       (babel-group-element-p group b))
      (babel-group-element-p
       group (babel-group-mul group a b)))
     (implies
      (and
       (babel-group-element-p group a)
       (babel-group-element-p group b)
       (babel-group-element-p group c))
      (equal
       (babel-group-mul
        group a (babel-group-mul group b c))
       (babel-group-mul
        group (babel-group-mul group a b) c))))))

(defun babel-group-p (group)
  (and
   (babel-group-element-p
    group (babel-group-one group))
   (babel-group-laws-p group)))

(defun-sk babel-group-commutative-law-p (group)
  (forall (a b)
    (implies
     (and
      (babel-group-element-p group a)
      (babel-group-element-p group b))
     (equal
      (babel-group-mul group a b)
      (babel-group-mul group b a)))))

(defun babel-commutative-group-p (group)
  (and
   (babel-group-p group)
   (babel-group-commutative-law-p group)))

(defun-sk babel-group-action-laws-p (group space action)
  (forall (g h x)
    (and
     (implies
      (and
       (babel-group-element-p group g)
       (babel-space-element-p space x))
      (babel-space-element-p
       space (babel-group-act action g x)))
     (implies
      (babel-space-element-p space x)
      (equal
       (babel-group-act
        action (babel-group-one group) x)
       x))
     (implies
      (and
       (babel-group-element-p group g)
       (babel-group-element-p group h)
       (babel-space-element-p space x))
      (equal
       (babel-group-act
        action (babel-group-mul group g h) x)
       (babel-group-act
        action g (babel-group-act action h x)))))))

(defun babel-group-action-p (group space action)
  (and
   (babel-group-p group)
   (babel-group-action-laws-p group space action)))

(defun-sk babel-group-orbit-p (group action x y)
  (exists (g)
    (and
     (babel-group-element-p group g)
     (equal (babel-group-act action g x) y))))

(defun babel-group-stabilizer-p (action x g)
  (equal (babel-group-act action g x) x))

;; Commutative-group and elementary group statements.

(defun-sk babel-formal-group-mul-rotate-statement ()
  (forall (group a b c)
    (implies
     (and
      (babel-commutative-group-p group)
      (babel-group-element-p group a)
      (babel-group-element-p group b)
      (babel-group-element-p group c))
     (equal
      (babel-group-mul
       group a (babel-group-mul group b c))
      (babel-group-mul
       group b (babel-group-mul group c a))))))

(defun-sk babel-formal-group-mul-left-cancel-statement ()
  (forall (group a b c)
    (implies
     (and
      (babel-group-p group)
      (babel-group-element-p group a)
      (babel-group-element-p group b)
      (babel-group-element-p group c)
      (equal
       (babel-group-mul group a b)
       (babel-group-mul group a c)))
     (equal b c))))

(defun-sk babel-formal-group-mul-right-cancel-statement ()
  (forall (group a b c)
    (implies
     (and
      (babel-group-p group)
      (babel-group-element-p group a)
      (babel-group-element-p group b)
      (babel-group-element-p group c)
      (equal
       (babel-group-mul group b a)
       (babel-group-mul group c a)))
     (equal b c))))

(defun-sk babel-formal-group-inv-inv-statement ()
  (forall (group a)
    (implies
     (and
      (babel-group-p group)
      (babel-group-element-p group a))
     (equal
      (babel-group-inv
       group (babel-group-inv group a))
      a))))

(defun-sk babel-formal-group-inv-mul-statement ()
  (forall (group a b)
    (implies
     (and
      (babel-group-p group)
      (babel-group-element-p group a)
      (babel-group-element-p group b))
     (equal
      (babel-group-inv
       group (babel-group-mul group a b))
      (babel-group-mul
       group
       (babel-group-inv group b)
       (babel-group-inv group a))))))

(defun-sk babel-formal-group-inv-eq-of-mul-eq-one-statement ()
  (forall (group a b)
    (implies
     (and
      (babel-group-p group)
      (babel-group-element-p group a)
      (babel-group-element-p group b)
      (equal
       (babel-group-mul group a b)
       (babel-group-one group)))
     (equal b (babel-group-inv group a)))))

;; Group-action, orbit, and stabilizer statements.

(defun-sk babel-formal-group-act-inv-statement ()
  (forall (group space action g x)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-group-element-p group g)
      (babel-space-element-p space x))
     (equal
      (babel-group-act
       action
       (babel-group-inv group g)
       (babel-group-act action g x))
      x))))

(defun-sk babel-formal-group-act-inv-r-statement ()
  (forall (group space action g x)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-group-element-p group g)
      (babel-space-element-p space x))
     (equal
      (babel-group-act
       action
       g
       (babel-group-act
        action (babel-group-inv group g) x))
      x))))

(defun-sk babel-formal-group-orbit-refl-statement ()
  (forall (group space action x)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x))
     (babel-group-orbit-p group action x x))))

(defun-sk babel-formal-group-orbit-sym-statement ()
  (forall (group space action x y)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-space-element-p space y)
      (babel-group-orbit-p group action x y))
     (babel-group-orbit-p group action y x))))

(defun-sk babel-formal-group-orbit-trans-statement ()
  (forall (group space action x y z)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-space-element-p space y)
      (babel-space-element-p space z)
      (babel-group-orbit-p group action x y)
      (babel-group-orbit-p group action y z))
     (babel-group-orbit-p group action x z))))

(defun-sk babel-formal-group-orbit-partition-statement ()
  (forall (group space action x y z)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-space-element-p space y)
      (babel-space-element-p space z)
      (babel-group-orbit-p group action x y))
     (equal
      (if (babel-group-orbit-p group action x z)
          t
        nil)
      (if (babel-group-orbit-p group action y z)
          t
        nil)))))

(defun-sk babel-formal-group-stabilizer-mul-statement ()
  (forall (group space action x g h)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-group-element-p group g)
      (babel-group-element-p group h)
      (babel-group-stabilizer-p action x g)
      (babel-group-stabilizer-p action x h))
     (babel-group-stabilizer-p
      action x (babel-group-mul group g h)))))

(defun-sk babel-formal-group-stabilizer-inv-statement ()
  (forall (group space action x g)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-group-element-p group g)
      (babel-group-stabilizer-p action x g))
     (babel-group-stabilizer-p
      action x (babel-group-inv group g)))))

(defun-sk babel-formal-group-stabilizer-one-statement ()
  (forall (group space action x)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x))
     (babel-group-stabilizer-p
      action x (babel-group-one group)))))

(defun-sk babel-formal-group-stabilizer-conjugate-statement ()
  (forall (group space action x g h)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-group-element-p group g)
      (babel-group-element-p group h)
      (babel-group-stabilizer-p action x h))
     (babel-group-stabilizer-p
      action
      (babel-group-act action g x)
      (babel-group-mul
       group
       (babel-group-mul group g h)
       (babel-group-inv group g))))))

(defun-sk
    babel-formal-group-stabilizer-conjugate-orbit-statement
    ()
  (forall (group space action x y g h)
    (implies
     (and
      (babel-group-action-p group space action)
      (babel-space-element-p space x)
      (babel-space-element-p space y)
      (babel-group-element-p group g)
      (babel-group-element-p group h)
      (equal (babel-group-act action g x) y))
     (equal
      (if (babel-group-stabilizer-p action y h)
          t
        nil)
      (if
          (babel-group-stabilizer-p
           action
           x
           (babel-group-mul
            group
            (babel-group-mul
             group
             (babel-group-inv group g)
             h)
            g))
          t
        nil)))))

(defun babel-formal-group-statement ()
  (and
   (babel-formal-group-mul-rotate-statement)
   (babel-formal-group-mul-left-cancel-statement)
   (babel-formal-group-mul-right-cancel-statement)
   (babel-formal-group-inv-inv-statement)
   (babel-formal-group-inv-mul-statement)
   (babel-formal-group-inv-eq-of-mul-eq-one-statement)
   (babel-formal-group-act-inv-statement)
   (babel-formal-group-act-inv-r-statement)
   (babel-formal-group-orbit-refl-statement)
   (babel-formal-group-orbit-sym-statement)
   (babel-formal-group-orbit-trans-statement)
   (babel-formal-group-orbit-partition-statement)
   (babel-formal-group-stabilizer-mul-statement)
   (babel-formal-group-stabilizer-inv-statement)
   (babel-formal-group-stabilizer-one-statement)
   (babel-formal-group-stabilizer-conjugate-statement)
   (babel-formal-group-stabilizer-conjugate-orbit-statement)))

(value-triple :itpeval-statement-checked)
:q
