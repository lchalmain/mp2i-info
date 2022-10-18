type direction = H | B | G | D

type profil = direction list
let est_sans_rebroussement g =
    let rec sans_reb = function
      | [] -> true
      | [B] -> false
      | H :: B :: q | B :: H:: q | G :: D :: q | D :: G :: q -> false
      | _ :: q -> sans_reb q
    in match g with
     | H :: q -> false
     | _ -> sans_reb g

     let () = assert (est_sans_rebroussement [B; D; B; D;H])
     let () = assert (not (est_sans_rebroussement [H; B; D; B; D; H]))
     let () = assert (not (est_sans_rebroussement [B; D; B; D; B]))
     let () = assert (not (est_sans_rebroussement [B; D; B; H; D; H]))

let est_une_vallee g = match g with
    | [] -> false
    | dir::q -> let rec descente desc profil = match profil with
                  | [] -> true
                  | G :: _ -> false
                  | D :: q -> descente desc q
                  | B :: q -> if desc then descente true q else false
                  | H :: q -> descente false q
                in  dir = B && est_sans_rebroussement g && descente true g

let () = assert (est_une_vallee [B; D; D; B; B; D; H; D; D; H; H])
let () = assert (not (est_une_vallee [B; D; D; B; B; D; H; D; B; D; H; H]))

let ex_vallee = [B; B; B; D; D; B; D; B; B; B; D; D; B; D; D; D; H; D; H; D; H; H; H; D; H; D; D; H]
let () = assert (est_une_vallee ex_vallee)

let voisin (x, y) d = match d with
    | D -> (x + 1, y)
    | G -> (x - 1, y)
    | H -> (x, y - 1)
    | B -> (x, y + 1)

let () = assert (voisin (5, 7) B = (5, 8))
let () = assert (voisin (0, 1) D = (1, 1))

let liste_des_points g =
    let rec liste point l = match l with
      | [] -> [point]
      | d :: q -> let nouv = voisin point d in point::(liste nouv q)
in liste (0, 0) g

let () = assert (liste_des_points [B; D; D; B; D; H] = [(0, 0); (0, 1); (1, 1); (2, 1); (2, 2); (3, 2); (3, 1)])

let est_simple g =
    let rec double dir liste = match liste with
      | [] -> false
      | d :: q when d = dir -> true
      | _::q -> double dir q
    in let rec parcours liste = match liste with
      | [] -> true
      | e :: q -> not (double e q) && parcours q
  in parcours (liste_des_points g)
  (* complexité : somme des k pour k = 0 to |g| -> quadratique *)

let () = assert (est_simple [B; D; D; B; D; H])
let () = assert (not (est_simple [B; D; D; B; G; H; D; H]))
let () = assert (est_simple ex_vallee)

let fond v = 
  (* v est une vallée - pas de G - descend puis monte *)
  let rec pente fd point = function
      | [] | H :: _ -> fd
      | D :: q -> pente fd (voisin point D) q
      | B :: q -> let n_fd = voisin point B in pente n_fd n_fd q
      | G :: _ -> failwith "v n'est pas une vallée"
    in pente (0, 0) (0, 0) v

let () = assert (fond [B; D; D; B; D; H] = (2, 2))
let () = assert (fond ex_vallee = (5, 8))

let plateaux v = let (x0, y0)::q = liste_des_points v in
    let rec plat x p y profil = match profil with
    (* identifie un plateau des abscisses a à p et de profondeur y *)
      | [] when x < p -> [(x, p, y)]
      | [] -> []
      | (u, v)::q when v = y -> plat x u y q (* tant qu'on reste à la même profondeur on augmente le plateau *)
      | (u, v)::q when x < p -> (x, p, y)::(plat u u v q) 
          (* changement de profondeur -> plateau ajouté en tête de liste + étude du reste du profil *)
      | (u, v)::q -> plat u u v q
  in plat x0 x0 y0 q

let ex_plateaux = plateaux ex_vallee

let decomposition_en_rectangles v = 
  let rec split desc liste_plateaux = match desc, liste_plateaux with
    (* sépare les plateaux de la phase descendante de ceux de la phase montante *)
    | desc, [] -> desc, []
    | [], p::q -> split [p] q
    | (x0, x1, y)::q, (d0, d1, z)::t -> if z > y then split ((d0, d1, z)::desc) t
                                        else desc, liste_plateaux
  in let rec fusionne descend monte = match descend, monte with
    (* fusionne les plateaux en triant par profondeur décroissante *)
    | [], _ -> monte
    | _, [] -> descend
    | (x0, x1, y)::q, (d0, d1, z)::t -> if y >= z then (x0, x1, y)::(fusionne q monte)
              (* si y = z, on trouvera le plateau d'abscisse minimale en premier *)
                                        else (d0, d1, z)::(fusionne descend t)
  in let desc_v, monte_v = split [] (plateaux v)
  in let l_plateaux = fusionne desc_v monte_v
  in let rec rectangles liste largeur = match liste with
    (* revoie les rectangles associés à une liste de plateaux triés *)
    | [] -> []    (* motif non matché *)
    | [(x0, x1, y)] -> [largeur + x1 - x0, -1]
    | (x0, x1, y)::(d0, d1, z)::[]  when y = z -> [largeur + x1 - x0 + d1 - d0, -1]
            (* x1 < d0 selon la fusion effectuée *)
    | (x0, x1, y)::(d0, d1, z)::(u0, u1, t)::q  when y = z -> 
            (d1 - x0, z - t)::(rectangles ((u0, u1, t)::q) (largeur + x1 - x0 + d1 - d0))
    | (x0, x1, y)::(d0, d1, z)::q ->
            (largeur + x1 - x0, y - z)::(rectangles ((d0, d1, z)::q) (largeur + x1 - x0))
  in rectangles l_plateaux 0

let ex_rectangles = decomposition_en_rectangles ex_vallee

let () = assert (ex_rectangles = [(3, 1); (6, 1); (7, 2); (8, 1); (11, 1); (13, -1)])
  
let hauteur_de_l_eau t v =
  let rectangles = decomposition_en_rectangles v in
  let rec hauteur rect tps rempli = match rect with
    | [] -> rempli
    | (larg, haut)::q when haut = -1 -> rempli +. tps /. (float_of_int larg)
    | (larg, haut)::q -> let h = tps /. (float_of_int larg) in
            if h > float_of_int haut then
                hauteur q (tps -. float_of_int (larg * haut)) (rempli +. float_of_int haut)
            else rempli +. tps /. (float_of_int larg)
  in hauteur rectangles t 0.
