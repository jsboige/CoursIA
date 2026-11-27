//! Crate pedagogique partagee des carnets Rust du depot CoursIA.
//!
//! Les carnets Rust affichent leurs resultats comme le ferait Python et
//! mesurent leurs temps d'execution. Ces deux gestes etaient recopies dans
//! chaque carnet, avec des variantes qui ont derive. Cette crate en fixe une
//! seule version, versionnee et testee, que les carnets importent par `:dep`.
//!
//! # Regle d'affichage
//!
//! Les fonctions `py_*` rendent la representation Python d'une valeur, pour
//! que la sortie d'un carnet Rust se compare ligne a ligne a celle du carnet
//! Python voisin : `True`/`False`, `[1, 2, 3]`, `['a', 'b']`, `(1, 2)`.
//!
//! # Regle de mesure
//!
//! `time_it` rend le resultat et sa duree, pour que la mesure soit toujours
//! prise de la meme facon et que les nombres d'un carnet a l'autre restent
//! comparables.
//!
//! # Utilisation dans un carnet
//!
//! ```ignore
//! :dep myia_nb = { path = "../RustSupport/myia_nb" }
//! ```
//!
//! Le `:dep` se place **en tete** du carnet : ajoute en cours de route, il
//! recompile la session et efface les variables deja saisies.

use std::fmt::Display;
use std::time::{Duration, Instant};

/// Rend un booleen comme Python l'ecrit : `True` ou `False`.
pub fn py_bool(b: bool) -> &'static str {
    if b {
        "True"
    } else {
        "False"
    }
}

/// Rend un booleen comme Python l'ecrit, en `String`.
///
/// Meme sortie que `py_bool`, type different : les carnets qui declaraient
/// leur aide en `String` s'y branchent par `use myia_nb::py_bool_string as py_bool;`,
/// sans toucher un seul appel.
pub fn py_bool_string(b: bool) -> String {
    py_bool(b).to_string()
}

/// Rend une liste de booleens comme Python l'ecrit : `[True, False]`.
pub fn py_bool_list(values: &[bool]) -> String {
    let parts: Vec<&str> = values.iter().map(|v| py_bool(*v)).collect();
    format!("[{}]", parts.join(", "))
}

/// Rend une sequence de valeurs affichables comme une liste Python : `[1, 2, 3]`.
///
/// Accepte les tranches de tout type qui sait s'afficher, ce qui couvre les
/// vecteurs de nombres, les tableaux fixes et les tranches de chaines simples.
pub fn py_list<T: Display>(items: &[T]) -> String {
    let parts: Vec<String> = items.iter().map(|v| v.to_string()).collect();
    format!("[{}]", parts.join(", "))
}

/// Rend des chaines comme Python les affiche dans une liste : `['a', 'b']`.
///
/// C'est la representation `repr` : les chaines sont entourees d'apostrophes,
/// la ou `py_list` les afficherait nues.
pub fn py_str_list(items: &[String]) -> String {
    let parts: Vec<String> = items.iter().map(|v| format!("'{}'", v)).collect();
    format!("[{}]", parts.join(", "))
}

/// Rend une suite de valeurs affichables comme un tuple Python : `(1, 2)`.
///
/// Le tuple a un seul element porte la virgule finale de Python : `(1,)`.
pub fn py_tup<T: Display>(items: &[T]) -> String {
    let parts: Vec<String> = items.iter().map(|v| v.to_string()).collect();
    if parts.len() == 1 {
        format!("({},)", parts[0])
    } else {
        format!("({})", parts.join(", "))
    }
}

/// Mesure la duree d'un calcul et rend le resultat avec sa duree.
///
/// Le calcul est execute une seule fois : la duree rendue est celle de cet
/// appel, pas une moyenne. Pour une moyenne, appeler `time_it` dans une boucle
/// et moyenner les durees rendues.
pub fn time_it<F, R>(f: F) -> (R, Duration)
where
    F: FnOnce() -> R,
{
    let start = Instant::now();
    let value = f();
    (value, start.elapsed())
}

/// Ecrit une duree en millisecondes avec trois decimales : `12.345 ms`.
///
/// Le format est fixe pour que les mesures s'alignent d'une execution et d'un
/// carnet a l'autre, et se recopient telles quelles dans une interpretation.
pub fn ms(elapsed: Duration) -> String {
    format!("{:.3} ms", elapsed.as_secs_f64() * 1000.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread::sleep;

    #[test]
    fn bool_prend_la_forme_python() {
        assert_eq!(py_bool(true), "True");
        assert_eq!(py_bool(false), "False");
    }

    #[test]
    fn bool_string_rend_le_meme_texte() {
        assert_eq!(py_bool_string(true), "True");
        assert_eq!(py_bool_string(false), "False");
        // Le type est bien String : la conversion est ce que la variante
        // `-> String` des carnets attendait.
        let s: String = py_bool_string(true);
        assert_eq!(s.len(), 4);
    }

    #[test]
    fn bool_list_prend_la_forme_python() {
        assert_eq!(py_bool_list(&[true, false, true]), "[True, False, True]");
        assert_eq!(py_bool_list(&[]), "[]");
    }

    #[test]
    fn list_prend_la_forme_python() {
        assert_eq!(py_list(&[1, 2, 3]), "[1, 2, 3]");
        assert_eq!(py_list(&[1.5, -2.0]), "[1.5, -2]");
        assert_eq!(py_list::<i64>(&[]), "[]");
    }

    #[test]
    fn str_list_porte_les_apostrophes() {
        let noms = vec!["alice".to_string(), "bob".to_string()];
        assert_eq!(py_str_list(&noms), "['alice', 'bob']");
    }

    #[test]
    fn tup_prend_la_forme_python() {
        assert_eq!(py_tup(&[1, 2]), "(1, 2)");
        assert_eq!(py_tup(&[1]), "(1,)");
        assert_eq!(py_tup::<i64>(&[]), "()");
    }

    #[test]
    fn time_it_rend_le_resultat_et_une_duree_positive() {
        let (value, elapsed) = time_it(|| {
            sleep(Duration::from_millis(5));
            42
        });
        assert_eq!(value, 42);
        assert!(
            elapsed >= Duration::from_millis(5),
            "duree mesuree trop courte"
        );
    }

    #[test]
    fn time_it_execute_le_calcul_une_seule_fois() {
        let mut compteur = 0;
        let (value, _) = time_it(|| {
            compteur += 1;
            compteur
        });
        assert_eq!(value, 1);
    }

    #[test]
    fn ms_a_trois_decimales() {
        assert_eq!(ms(Duration::from_micros(12345)), "12.345 ms");
        assert_eq!(ms(Duration::from_secs(1)), "1000.000 ms");
    }
}
