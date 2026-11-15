;; Statement-only formalization of thousand-theorems corpus artifact Q4878586,
;; "Beck's monadicity theorem": a right adjoint that creates coequalizers of
;; its G-split pairs is monadic, meaning that it admits a left adjoint whose
;; comparison functor is an equivalence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Categories and functors are represented by tame function objects over
;; arbitrary ACL2 objects. DEFUN-SK retains all universal-property and
;; essential-surjectivity witnesses inside their source quantifier scopes.

(defun q4878586-app1 (function x)
  (apply$ function (list x)))

(defun q4878586-app2 (function x y)
  (apply$ function (list x y)))

(defun q4878586-object-p (objects x)
  (and (tamep-functionp objects)
       (q4878586-app1 objects x)))

(defun q4878586-morphism-p (morphisms f)
  (and (tamep-functionp morphisms)
       (q4878586-app1 morphisms f)))

(defun q4878586-hom-p (morphisms domain codomain f x y)
  (and (q4878586-morphism-p morphisms f)
       (equal (q4878586-app1 domain f) x)
       (equal (q4878586-app1 codomain f) y)))

(defun q4878586-category-law-at
    (objects morphisms domain codomain identity compose tuple)
  (let* ((w (nth 0 tuple))
         (x (nth 1 tuple))
         (y (nth 2 tuple))
         (z (nth 3 tuple))
         (f (nth 4 tuple))
         (g (nth 5 tuple))
         (h (nth 6 tuple))
         (df (q4878586-app1 domain f))
         (cf (q4878586-app1 codomain f)))
    (and
     (implies
      (q4878586-object-p objects x)
      (q4878586-hom-p
       morphisms domain codomain
       (q4878586-app1 identity x) x x))
     (implies
      (q4878586-morphism-p morphisms f)
      (and
       (q4878586-object-p objects df)
       (q4878586-object-p objects cf)
       (equal
        (q4878586-app2
         compose (q4878586-app1 identity cf) f)
        f)
       (equal
        (q4878586-app2
         compose f (q4878586-app1 identity df))
        f)))
     (implies
      (and
       (q4878586-hom-p morphisms domain codomain f x y)
       (q4878586-hom-p morphisms domain codomain g y z))
      (q4878586-hom-p
       morphisms domain codomain
       (q4878586-app2 compose g f) x z))
     (implies
      (and
       (q4878586-hom-p morphisms domain codomain f w x)
       (q4878586-hom-p morphisms domain codomain g x y)
       (q4878586-hom-p morphisms domain codomain h y z))
      (equal
       (q4878586-app2
        compose h (q4878586-app2 compose g f))
       (q4878586-app2
        compose (q4878586-app2 compose h g) f))))))

(defun-sk q4878586-category-laws-p
    (objects morphisms domain codomain identity compose)
  (forall (tuple)
    (q4878586-category-law-at
     objects morphisms domain codomain identity compose tuple)))

(defun q4878586-category-p
    (objects morphisms domain codomain identity compose)
  (and
   (tamep-functionp objects)
   (tamep-functionp morphisms)
   (tamep-functionp domain)
   (tamep-functionp codomain)
   (tamep-functionp identity)
   (tamep-functionp compose)
   (q4878586-category-laws-p
    objects morphisms domain codomain identity compose)))

(defun q4878586-functor-law-at
    (source-objects source-morphisms source-domain source-codomain
     source-identity source-compose
     target-objects target-morphisms target-domain target-codomain
     target-identity target-compose object-map morphism-map tuple)
  (let* ((x (nth 0 tuple))
         (y (nth 1 tuple))
         (z (nth 2 tuple))
         (f (nth 3 tuple))
         (g (nth 4 tuple))
         (fx (q4878586-app1 object-map x))
         (fy (q4878586-app1 object-map y))
         (fz (q4878586-app1 object-map z))
         (ff (q4878586-app1 morphism-map f))
         (fg (q4878586-app1 morphism-map g)))
    (and
     (implies
      (q4878586-object-p source-objects x)
      (and
       (q4878586-object-p target-objects fx)
       (equal
        (q4878586-app1
         morphism-map (q4878586-app1 source-identity x))
        (q4878586-app1 target-identity fx))))
     (implies
      (q4878586-hom-p
       source-morphisms source-domain source-codomain f x y)
      (q4878586-hom-p
       target-morphisms target-domain target-codomain ff fx fy))
     (implies
      (and
       (q4878586-hom-p
        source-morphisms source-domain source-codomain f x y)
       (q4878586-hom-p
        source-morphisms source-domain source-codomain g y z))
      (equal
       (q4878586-app1
        morphism-map (q4878586-app2 source-compose g f))
       (q4878586-app2 target-compose fg ff)))
     (implies
      (and
       (q4878586-object-p source-objects x)
       (q4878586-object-p source-objects y)
       (q4878586-object-p source-objects z))
      (and
       (q4878586-object-p target-objects fx)
       (q4878586-object-p target-objects fy)
       (q4878586-object-p target-objects fz))))))

(defun-sk q4878586-functor-laws-p
    (source-objects source-morphisms source-domain source-codomain
     source-identity source-compose
     target-objects target-morphisms target-domain target-codomain
     target-identity target-compose object-map morphism-map)
  (forall (tuple)
    (q4878586-functor-law-at
     source-objects source-morphisms source-domain source-codomain
     source-identity source-compose
     target-objects target-morphisms target-domain target-codomain
     target-identity target-compose object-map morphism-map tuple)))

(defun q4878586-functor-p
    (source-objects source-morphisms source-domain source-codomain
     source-identity source-compose
     target-objects target-morphisms target-domain target-codomain
     target-identity target-compose object-map morphism-map)
  (and
   (tamep-functionp object-map)
   (tamep-functionp morphism-map)
   (q4878586-functor-laws-p
    source-objects source-morphisms source-domain source-codomain
    source-identity source-compose
    target-objects target-morphisms target-domain target-codomain
    target-identity target-compose object-map morphism-map)))

(defun q4878586-adjunction-law-at
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism g-object g-morphism unit counit tuple)
  (let* ((x (nth 0 tuple))
         (y (nth 1 tuple))
         (u (nth 2 tuple))
         (v (nth 3 tuple))
         (cf (nth 4 tuple))
         (df (nth 5 tuple))
         (fx (q4878586-app1 f-object x))
         (gu (q4878586-app1 g-object u))
         (eta-x (q4878586-app1 unit x))
         (eta-y (q4878586-app1 unit y))
         (eps-u (q4878586-app1 counit u))
         (eps-v (q4878586-app1 counit v)))
    (and
     (implies
      (q4878586-object-p c-objects x)
      (q4878586-hom-p
       c-morphisms c-domain c-codomain eta-x x
       (q4878586-app1 g-object fx)))
     (implies
      (q4878586-hom-p c-morphisms c-domain c-codomain cf x y)
      (equal
       (q4878586-app2 c-compose eta-y cf)
       (q4878586-app2
        c-compose
        (q4878586-app1
         g-morphism (q4878586-app1 f-morphism cf))
        eta-x)))
     (implies
      (q4878586-object-p d-objects u)
      (q4878586-hom-p
       d-morphisms d-domain d-codomain eps-u
       (q4878586-app1 f-object gu) u))
     (implies
      (q4878586-hom-p d-morphisms d-domain d-codomain df u v)
      (equal
       (q4878586-app2
        d-compose eps-v
        (q4878586-app1
         f-morphism (q4878586-app1 g-morphism df)))
       (q4878586-app2 d-compose df eps-u)))
     (implies
      (q4878586-object-p c-objects x)
      (equal
       (q4878586-app2
        d-compose
        (q4878586-app1 counit fx)
        (q4878586-app1 f-morphism eta-x))
       (q4878586-app1 d-identity fx)))
     (implies
      (q4878586-object-p d-objects u)
      (equal
       (q4878586-app2
        c-compose
        (q4878586-app1 g-morphism eps-u)
        (q4878586-app1 unit gu))
       (q4878586-app1 c-identity gu))))))

(defun-sk q4878586-adjunction-laws-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism g-object g-morphism unit counit)
  (forall (tuple)
    (q4878586-adjunction-law-at
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism g-object g-morphism unit counit tuple)))

(defun q4878586-adjunction-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism g-object g-morphism unit counit)
  (and
   (tamep-functionp unit)
   (tamep-functionp counit)
   (q4878586-adjunction-laws-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain d-identity d-compose
    f-object f-morphism g-object g-morphism unit counit)))

(defun q4878586-split-coequalizer-witness-p
    (objects morphisms domain codomain identity compose
     f g witness)
  (let ((z (nth 0 witness))
        (projection (nth 1 witness))
        (right-section (nth 2 witness))
        (left-section (nth 3 witness))
        (x (q4878586-app1 domain f))
        (y (q4878586-app1 codomain f)))
    (and
     (true-listp witness)
     (equal (len witness) 4)
     (q4878586-object-p objects z)
     (q4878586-hom-p
      morphisms domain codomain projection y z)
     (q4878586-hom-p
      morphisms domain codomain right-section z y)
     (q4878586-hom-p
      morphisms domain codomain left-section y x)
     (equal
      (q4878586-app2 compose projection f)
      (q4878586-app2 compose projection g))
     (equal
      (q4878586-app2 compose projection right-section)
      (q4878586-app1 identity z))
     (equal
      (q4878586-app2 compose g left-section)
      (q4878586-app1 identity y))
     (equal
      (q4878586-app2 compose f left-section)
      (q4878586-app2 compose right-section projection)))))

(defun-sk q4878586-split-coequalizer-exists-p
    (objects morphisms domain codomain identity compose f g)
  (exists (witness)
    (q4878586-split-coequalizer-witness-p
     objects morphisms domain codomain identity compose
     f g witness)))

(defun q4878586-g-split-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     g-morphism f g)
  (q4878586-split-coequalizer-exists-p
   c-objects c-morphisms c-domain c-codomain c-identity c-compose
   (q4878586-app1 g-morphism f)
   (q4878586-app1 g-morphism g)))

(defun q4878586-cofork-p
    (objects morphisms domain codomain compose f g z projection)
  (let ((x (q4878586-app1 domain f))
        (y (q4878586-app1 codomain f)))
    (and
     (q4878586-object-p objects z)
     (q4878586-hom-p morphisms domain codomain f x y)
     (q4878586-hom-p morphisms domain codomain g x y)
     (q4878586-hom-p morphisms domain codomain projection y z)
     (equal
      (q4878586-app2 compose projection f)
      (q4878586-app2 compose projection g)))))

(defun q4878586-factor-unique-law-at
    (morphisms domain codomain compose
     source projection target map factor candidate)
  (implies
   (and
    (q4878586-hom-p
     morphisms domain codomain candidate source target)
    (equal
     (q4878586-app2 compose candidate projection)
     map))
   (equal candidate factor)))

(defun-sk q4878586-factor-unique-p
    (morphisms domain codomain compose
     source projection target map factor)
  (forall (candidate)
    (q4878586-factor-unique-law-at
     morphisms domain codomain compose
     source projection target map factor candidate)))

(defun q4878586-factor-p
    (morphisms domain codomain compose
     source projection target map factor)
  (and
   (q4878586-hom-p
    morphisms domain codomain factor source target)
   (equal
    (q4878586-app2 compose factor projection)
    map)
   (q4878586-factor-unique-p
    morphisms domain codomain compose
    source projection target map factor)))

(defun-sk q4878586-factor-exists-p
    (morphisms domain codomain compose
     source projection target map)
  (exists (factor)
    (q4878586-factor-p
     morphisms domain codomain compose
     source projection target map factor)))

(defun q4878586-coequalizer-law-at
    (objects morphisms domain codomain compose
     f g source projection tuple)
  (let ((target (nth 0 tuple))
        (map (nth 1 tuple)))
    (implies
     (q4878586-cofork-p
      objects morphisms domain codomain compose f g target map)
     (q4878586-factor-exists-p
      morphisms domain codomain compose
      source projection target map))))

(defun-sk q4878586-coequalizer-laws-p
    (objects morphisms domain codomain compose
     f g source projection)
  (forall (tuple)
    (q4878586-coequalizer-law-at
     objects morphisms domain codomain compose
     f g source projection tuple)))

(defun q4878586-coequalizer-p
    (objects morphisms domain codomain compose
     f g source projection)
  (and
   (q4878586-cofork-p
    objects morphisms domain codomain compose
    f g source projection)
   (q4878586-coequalizer-laws-p
    objects morphisms domain codomain compose
    f g source projection)))

(defun q4878586-lift-witness-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism f g target target-projection witness)
  (let* ((source (nth 0 witness))
         (projection (nth 1 witness))
         (forward (nth 2 witness))
         (backward (nth 3 witness))
         (g-source (q4878586-app1 g-object source))
         (g-projection (q4878586-app1 g-morphism projection)))
    (and
     (true-listp witness)
     (equal (len witness) 4)
     (q4878586-object-p c-objects g-source)
     (q4878586-object-p c-objects target)
     (q4878586-cofork-p
      d-objects d-morphisms d-domain d-codomain d-compose
      f g source projection)
     (q4878586-hom-p
      c-morphisms c-domain c-codomain forward g-source target)
     (q4878586-hom-p
      c-morphisms c-domain c-codomain backward target g-source)
     (equal
      (q4878586-app2 c-compose forward g-projection)
      target-projection)
     (equal
      (q4878586-app2 c-compose backward target-projection)
      g-projection)
     (equal
      (q4878586-app2 c-compose backward forward)
      (q4878586-app1 c-identity g-source))
     (equal
      (q4878586-app2 c-compose forward backward)
      (q4878586-app1 c-identity target)))))

(defun-sk q4878586-lift-exists-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism f g target target-projection)
  (exists (witness)
    (q4878586-lift-witness-p
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism f g target target-projection witness)))

(defun q4878586-creates-law-at
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism f g tuple)
  (let* ((source (nth 0 tuple))
         (projection (nth 1 tuple))
         (target (nth 2 tuple))
         (target-projection (nth 3 tuple))
         (gf (q4878586-app1 g-morphism f))
         (gg (q4878586-app1 g-morphism g))
         (g-source (q4878586-app1 g-object source))
         (g-projection (q4878586-app1 g-morphism projection)))
    (and
     (implies
      (and
       (q4878586-cofork-p
        d-objects d-morphisms d-domain d-codomain d-compose
        f g source projection)
       (q4878586-coequalizer-p
        c-objects c-morphisms c-domain c-codomain c-compose
        gf gg g-source g-projection))
      (q4878586-coequalizer-p
       d-objects d-morphisms d-domain d-codomain d-compose
       f g source projection))
     (implies
      (q4878586-coequalizer-p
       c-objects c-morphisms c-domain c-codomain c-compose
       gf gg target target-projection)
      (q4878586-lift-exists-p
       c-objects c-morphisms c-domain c-codomain c-identity c-compose
       d-objects d-morphisms d-domain d-codomain d-compose
       g-object g-morphism f g target target-projection)))))

(defun-sk q4878586-creates-coequalizer-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism f g)
  (forall (tuple)
    (q4878586-creates-law-at
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism f g tuple)))

(defun q4878586-creates-split-law-at
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism tuple)
  (let ((x (nth 0 tuple))
        (y (nth 1 tuple))
        (f (nth 2 tuple))
        (g (nth 3 tuple)))
    (implies
     (and
      (q4878586-hom-p d-morphisms d-domain d-codomain f x y)
      (q4878586-hom-p d-morphisms d-domain d-codomain g x y)
      (q4878586-g-split-p
       c-objects c-morphisms c-domain c-codomain
       c-identity c-compose g-morphism f g))
     (q4878586-creates-coequalizer-p
      c-objects c-morphisms c-domain c-codomain c-identity c-compose
      d-objects d-morphisms d-domain d-codomain d-compose
      g-object g-morphism f g))))

(defun-sk q4878586-creates-g-split-coequalizers-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism)
  (forall (tuple)
    (q4878586-creates-split-law-at
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism tuple)))

(defun q4878586-algebra-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     f-object f-morphism g-object g-morphism unit counit object action)
  (let* ((f-object-value (q4878586-app1 f-object object))
         (gf-object
          (q4878586-app1 g-object f-object-value))
         (mu
          (q4878586-app1
           g-morphism (q4878586-app1 counit f-object-value)))
         (t-action
          (q4878586-app1
           g-morphism (q4878586-app1 f-morphism action))))
    (and
     (q4878586-object-p c-objects object)
     (q4878586-hom-p
      c-morphisms c-domain c-codomain action gf-object object)
     (equal
      (q4878586-app2
       c-compose action (q4878586-app1 unit object))
      (q4878586-app1 c-identity object))
     (equal
      (q4878586-app2 c-compose action mu)
      (q4878586-app2 c-compose action t-action)))))

(defun q4878586-algebra-hom-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     f-object f-morphism g-object g-morphism unit counit
     source source-action target target-action map)
  (and
   (q4878586-algebra-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    f-object f-morphism g-object g-morphism unit counit
    source source-action)
   (q4878586-algebra-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    f-object f-morphism g-object g-morphism unit counit
    target target-action)
   (q4878586-hom-p
    c-morphisms c-domain c-codomain map source target)
   (equal
    (q4878586-app2
     c-compose target-action
     (q4878586-app1
      g-morphism (q4878586-app1 f-morphism map)))
    (q4878586-app2 c-compose map source-action))))

(defun q4878586-comparison-action (g-morphism counit object)
  (q4878586-app1
   g-morphism (q4878586-app1 counit object)))

(defun q4878586-comparison-full-witness-p
    (d-morphisms d-domain d-codomain g-morphism
     source target algebra-map witness)
  (and
   (q4878586-hom-p
    d-morphisms d-domain d-codomain witness source target)
   (equal (q4878586-app1 g-morphism witness) algebra-map)))

(defun-sk q4878586-comparison-full-witness-exists-p
    (d-morphisms d-domain d-codomain g-morphism
     source target algebra-map)
  (exists (witness)
    (q4878586-comparison-full-witness-p
     d-morphisms d-domain d-codomain g-morphism
     source target algebra-map witness)))

(defun q4878586-comparison-full-law-at
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain
     f-object f-morphism g-object g-morphism unit counit tuple)
  (let* ((source (nth 0 tuple))
         (target (nth 1 tuple))
         (algebra-map (nth 2 tuple))
         (g-source (q4878586-app1 g-object source))
         (g-target (q4878586-app1 g-object target))
         (source-action
          (q4878586-comparison-action g-morphism counit source))
         (target-action
          (q4878586-comparison-action g-morphism counit target)))
    (implies
     (and
      (q4878586-object-p d-objects source)
      (q4878586-object-p d-objects target)
      (q4878586-algebra-hom-p
       c-objects c-morphisms c-domain c-codomain c-identity c-compose
       f-object f-morphism g-object g-morphism unit counit
       g-source source-action g-target target-action algebra-map))
     (q4878586-comparison-full-witness-exists-p
      d-morphisms d-domain d-codomain g-morphism
      source target algebra-map))))

(defun-sk q4878586-comparison-full-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain
     f-object f-morphism g-object g-morphism unit counit)
  (forall (tuple)
    (q4878586-comparison-full-law-at
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain
     f-object f-morphism g-object g-morphism unit counit tuple)))

(defun q4878586-comparison-faithful-law-at
    (d-morphisms d-domain d-codomain g-morphism tuple)
  (let ((x (nth 0 tuple))
        (y (nth 1 tuple))
        (f (nth 2 tuple))
        (g (nth 3 tuple)))
    (implies
     (and
      (q4878586-hom-p d-morphisms d-domain d-codomain f x y)
      (q4878586-hom-p d-morphisms d-domain d-codomain g x y)
      (equal
       (q4878586-app1 g-morphism f)
       (q4878586-app1 g-morphism g)))
     (equal f g))))

(defun-sk q4878586-comparison-faithful-p
    (d-morphisms d-domain d-codomain g-morphism)
  (forall (tuple)
    (q4878586-comparison-faithful-law-at
     d-morphisms d-domain d-codomain g-morphism tuple)))

(defun q4878586-essential-witness-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects
     f-object f-morphism g-object g-morphism unit counit
     object action witness)
  (let* ((d-object (nth 0 witness))
         (forward (nth 1 witness))
         (backward (nth 2 witness))
         (g-d-object (q4878586-app1 g-object d-object))
         (comparison-action
          (q4878586-comparison-action
           g-morphism counit d-object)))
    (and
     (true-listp witness)
     (equal (len witness) 3)
     (q4878586-object-p d-objects d-object)
     (q4878586-algebra-hom-p
      c-objects c-morphisms c-domain c-codomain c-identity c-compose
      f-object f-morphism g-object g-morphism unit counit
      object action g-d-object comparison-action forward)
     (q4878586-algebra-hom-p
      c-objects c-morphisms c-domain c-codomain c-identity c-compose
      f-object f-morphism g-object g-morphism unit counit
      g-d-object comparison-action object action backward)
     (equal
      (q4878586-app2 c-compose backward forward)
      (q4878586-app1 c-identity object))
     (equal
      (q4878586-app2 c-compose forward backward)
      (q4878586-app1 c-identity g-d-object)))))

(defun-sk q4878586-essential-witness-exists-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects
     f-object f-morphism g-object g-morphism unit counit
     object action)
  (exists (witness)
    (q4878586-essential-witness-p
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects
     f-object f-morphism g-object g-morphism unit counit
     object action witness)))

(defun q4878586-comparison-essential-law-at
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects
     f-object f-morphism g-object g-morphism unit counit tuple)
  (let ((object (nth 0 tuple))
        (action (nth 1 tuple)))
    (implies
     (q4878586-algebra-p
      c-objects c-morphisms c-domain c-codomain c-identity c-compose
      f-object f-morphism g-object g-morphism unit counit
      object action)
     (q4878586-essential-witness-exists-p
      c-objects c-morphisms c-domain c-codomain c-identity c-compose
      d-objects
      f-object f-morphism g-object g-morphism unit counit
      object action))))

(defun-sk q4878586-comparison-essentially-surjective-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects
     f-object f-morphism g-object g-morphism unit counit)
  (forall (tuple)
    (q4878586-comparison-essential-law-at
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects
     f-object f-morphism g-object g-morphism unit counit tuple)))

(defun q4878586-comparison-equivalence-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain
     f-object f-morphism g-object g-morphism unit counit)
  (and
   (q4878586-comparison-full-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain
    f-object f-morphism g-object g-morphism unit counit)
   (q4878586-comparison-faithful-p
    d-morphisms d-domain d-codomain g-morphism)
   (q4878586-comparison-essentially-surjective-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects
    f-object f-morphism g-object g-morphism unit counit)))

(defun q4878586-monadic-witness-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     g-object g-morphism
     left-object left-morphism left-unit left-counit)
  (and
   (q4878586-functor-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain d-identity d-compose
    left-object left-morphism)
   (q4878586-adjunction-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain d-identity d-compose
    left-object left-morphism g-object g-morphism
    left-unit left-counit)
   (q4878586-comparison-equivalence-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain
    left-object left-morphism g-object g-morphism
    left-unit left-counit)))

(defun-sk q4878586-monadic-right-adjoint-p
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     g-object g-morphism)
  (exists
   (left-object left-morphism left-unit left-counit)
   (q4878586-monadic-witness-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain d-identity d-compose
    g-object g-morphism
    left-object left-morphism left-unit left-counit)))

(defun thousand-theorems-q4878586-becks-monadicity-theorem-statement
    (c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism g-object g-morphism unit counit)
  (implies
   (and
    (q4878586-category-p
     c-objects c-morphisms c-domain c-codomain c-identity c-compose)
    (q4878586-category-p
     d-objects d-morphisms d-domain d-codomain d-identity d-compose)
    (q4878586-functor-p
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism)
    (q4878586-functor-p
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     g-object g-morphism)
    (q4878586-adjunction-p
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-identity d-compose
     f-object f-morphism g-object g-morphism unit counit)
    (q4878586-creates-g-split-coequalizers-p
     c-objects c-morphisms c-domain c-codomain c-identity c-compose
     d-objects d-morphisms d-domain d-codomain d-compose
     g-object g-morphism))
   (q4878586-monadic-right-adjoint-p
    c-objects c-morphisms c-domain c-codomain c-identity c-compose
    d-objects d-morphisms d-domain d-codomain d-identity d-compose
    g-object g-morphism)))

(value-triple :itpeval-statement-checked)
:q
