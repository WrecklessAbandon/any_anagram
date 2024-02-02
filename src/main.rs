/// # anagram
/// My solution to the Trust Pilot anagram phrase problem.
/// The fastest way to learn something new is to dive into it and I used this
/// problem as a means to learn Rust.
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::collections::{HashMap, HashSet};
use std::ops::Index;
use async_std::task;
use num_cpus;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::time::Instant;
use std::process;
use std::cmp::Ordering;

#[derive(Clone, Debug)]
struct AnagramSearch {
    anagram_chars_search: HashMap<char, u32>, // The sorted anagram chars to search for
}

#[derive(Clone, Debug)]
struct AnagramSearchLookups {
    md5_checksums: HashSet<md5::Digest>, // Checksum to compare anagram phrases
    anagrams_sorted_vec: Vec<String>, // Sorted anagram, to maintain order
    anagrams_sorted_map: HashMap<String, Vec<String>>, // Sorted anagram -> Multiple Words
    anagrams_sorted_chars: HashMap<String, HashMap<char, u32>>, // Sorted anagram -> # Characters
}

#[derive(Clone, Debug)]
struct AnagramSolutionMetrics {
    anagram_phrase_checksum: md5::Digest,
    anagram_phrase_time: std::time::Instant,
}

/// Who doesn't like metrics? This data structure contains all of the interesting
/// factoids that will be printed out at the end of the program's run.
#[derive(Clone, Debug)]
struct AnagramMetrics {
    anagram_phrase_solution: HashMap<String, AnagramSolutionMetrics>, // The anagram phrase solutions
    anagram_phrases_incomplete: u64, // How many incomplete phrases couldn't match the anagram characters
    anagram_roots_exhausted: u64, // How many anagram root words have been exhaustively calculated
    anagram_phrases_found: u64, // How many suitable phrases were found and calculated as MD5
    anagram_phrase_max_depth: u32, // The largest number of suitable words had fit in a the anagram phrase
    is_done: bool, // Signaling that the metrics for the root word is complete and can be tallied
}

/// Retrieves the anagram phrase from resources/anagram
/// and sorts it as an anagram phrase while omitting the spaces.
fn get_anagram() -> (String, String) {
    let filename = String::from("resources/anagram");
    let f = File::open(filename).unwrap();
    let mut f = BufReader::new(f);
    let mut buffer = String::new();
    let line: Result<usize, std::io::Error> = f.read_line(&mut buffer);

    if line.is_ok() {
        let mut chars: Vec<char> = buffer.chars().collect();
        chars.retain(|&x| x != ' ');
        chars.sort();
        return (chars.iter().collect::<String>(), buffer)
    }

    return ("".to_string(), "".to_string());
}

// Get the map of sorted words to words.
// EG:
// abcer <-- Key
// --brace <-- Value
// --crabe <-- Value
fn get_anagram_map() -> HashMap<String, HashSet<String>> {
    let filename = String::from("resources/wordlist");
    let f = File::open(filename).unwrap();
    let f = BufReader::new(f);

    let mut anagrams: HashMap<String, HashSet<String>> = HashMap::new();

    for line in f.lines() {
        let line = line.expect("Could not read line from file");
        let value : String = String::from(&line);
        let mut chars: Vec<char> = value.clone().chars().collect();
        
        chars.sort();
        let anagram_sorted: String = chars.iter().collect();
        
        anagrams.entry(anagram_sorted).and_modify(|hs| {hs.insert(value.clone());}).or_insert(HashSet::from([value]));
    }
    return anagrams;
}

// Determine if the character count is within the limit of the given character sequence.
// EG:
// If the letter Y has 6 instances then the comparison of Y having 5 instances will return true.
// If the ltter X has 2 instances then the comparison of X having 3 instances will return false.
fn contains_chars(required: &HashMap<char, u32>, compare: &HashMap<char, u32>) -> bool {
    if compare.len() > required.len() {
        return false;
    }

    for (compare_char, compare_count) in compare {
        let required_count = required.get(&compare_char);
        if required_count.is_none() || compare_count > required_count.unwrap() {
            return false;
        }
    }
    return true;
}

// Count the characters from a string sequence
fn count_chars(char_sequence: &String) -> HashMap<char, u32> {
    let mut char_hash : HashMap<char, u32> = HashMap::new();

    for char in char_sequence.chars() {
        *char_hash.entry(char).or_insert(0) += 1;
    }

    return char_hash;
}

// Add the character count to another character count
fn add_chars(source: &mut HashMap<char, u32>, add: &HashMap<char, u32>) {
    for (char_key, char_count) in add.iter() {
        source.entry(*char_key).and_modify(|counter| *counter += *char_count).or_insert(*char_count);
    }
}

// Subtract the character count from another character count.
// This will return false if the subtracted character count is greater
// than the source; character counts can't be negative.
fn subtract_chars(source: &mut HashMap<char, u32>, subtract: &HashMap<char, u32>) -> bool {
    if !contains_chars(&source, &subtract) {
        return false;
    }

    for (char_key, char_count) in subtract.iter() {
        source.entry(*char_key).and_modify(|counter| *counter -= *char_count);

        let char_value = source.get(char_key);
        if char_value == Some(&0) {
            source.remove(char_key);
        }
    }

    return true;
}

// Used for metrics & reporting
fn add_metrics(total_metric: &mut AnagramMetrics, add_metric: AnagramMetrics) {
    total_metric.anagram_roots_exhausted += 1;
    total_metric.anagram_phrases_incomplete += add_metric.anagram_phrases_incomplete;
    total_metric.anagram_phrases_found += add_metric.anagram_phrases_found;
    if total_metric.anagram_phrase_max_depth < add_metric.anagram_phrase_max_depth {
        total_metric.anagram_phrase_max_depth = add_metric.anagram_phrase_max_depth;
    }
}

// The entry point for the anagram phrase solution.
fn search_anagram_phrases(mut anagram_search: AnagramSearch, anagram_search_lookups: AnagramSearchLookups) {
    // Technical stuff to control concurrency
    let num_cores = num_cpus::get();
    let num_concurrent: usize = num_cores;
    let mut count_concurrent: usize = 0;
    let mut count_success: u32 = 0;
    let mut metrics: AnagramMetrics = AnagramMetrics { 
        anagram_phrase_solution: HashMap::new(),
        anagram_phrases_incomplete: 0,
        anagram_roots_exhausted: 0,
        anagram_phrases_found: 0, 
        anagram_phrase_max_depth: 0,
        is_done: false,};

    // Performance measuring metrics. Keep this immediately above the loop.
    // For best measurements, disable the print statements until the end.
    let start_time: Instant = Instant::now();

    let (tx, rx): (Sender<AnagramMetrics>, Receiver<AnagramMetrics>) = channel();

    // Loop over all sorted anagrams and insert them recursively.
    // The actual words from the anagrams will permutate later.
    for (current_anagram_sorted_index, current_anagram_sorted) in anagram_search_lookups.anagrams_sorted_vec.iter().enumerate() {
        // Keep the user informed of the progress
        println!("Processing root: {}/{}, anagram sorted: {}, len: {}",
            current_anagram_sorted_index+1, // Use natural numbers
            anagram_search_lookups.anagrams_sorted_vec.len(),
            current_anagram_sorted,
            current_anagram_sorted.len());

        let current_anagram_char_count: &HashMap<char, u32> = anagram_search_lookups.anagrams_sorted_chars.get(current_anagram_sorted).unwrap();

        if !subtract_chars(&mut anagram_search.anagram_chars_search, current_anagram_char_count) {
            continue;
        }

        // The cloning is necessary for the asynchronous operations.
        let anagram_search_clone: AnagramSearch = anagram_search.clone();
        let anagram_search_lookups_clone: AnagramSearchLookups = anagram_search_lookups.clone();
        let tx_clone: Sender<AnagramMetrics> = tx.clone();
        let anagram_sorted_clone: String = current_anagram_sorted.clone();

        task::spawn(async move {
            async_traverse_anagram_phrases(
                anagram_search_clone,
                anagram_search_lookups_clone,
                anagram_sorted_clone,
                current_anagram_sorted_index,
                tx_clone,
            ).await});
                        
        add_chars(&mut anagram_search.anagram_chars_search, current_anagram_char_count);

        // TODO: Code can be refactored here and complexity reduced but it's not required due to diminishing returns.
        count_concurrent += 1;
        if count_concurrent >= num_concurrent {
            let metrics_received = rx.recv().unwrap();
            metrics.anagram_phrase_solution.extend(metrics_received.anagram_phrase_solution.clone().into_iter());
            if metrics_received.is_done {
                count_concurrent -= 1;
                add_metrics(&mut metrics, metrics_received);
            } else {
                // TODO: Complexity. This is ugly, the code can be refactored to get rid of this awful else branch
                // Fix this later to reduce the code complexity and ugliness.
                let solution_success = metrics_received.anagram_phrase_solution.len() as u32;
                count_success += solution_success;
            }
            if count_success >= (anagram_search_lookups.md5_checksums.len() as u32) {
                println!(
                    "--Metrics from exhausted anagram roots--\n\
                    - Anagram Roots Exhausted: {}\n\
                    - Phrases Computed: {}\n\
                    - Phrases Invalid: {}\n\
                    - Max Phrase Length: {}\n\
                    - Tasks in progress (no metrics reported): {}",
                    metrics.anagram_phrases_found.to_formatted_string(&Locale::en),
                    metrics.anagram_phrases_incomplete.to_formatted_string(&Locale::en),
                    metrics.anagram_phrase_max_depth,
                    metrics.anagram_roots_exhausted,
                    count_concurrent);
                metrics.anagram_phrase_solution.iter().for_each(|(phrase, solution_metrics)| 
                    println!("{:?} : {}, time to find: {:?}", solution_metrics.anagram_phrase_checksum, phrase, solution_metrics.anagram_phrase_time.duration_since(start_time)));
                // Other threads may be running, it is possible to do a graceful exit but that yields virtually no benefit
                // and requires more complexity in the form of code. Just exit the process and call it a win.
                process::exit(0);
            }
        }
    }

    loop {
        if count_concurrent == 0 {
            break;
        }

        if count_concurrent >= num_concurrent {
            let metrics_received = rx.recv().unwrap();
            count_success += metrics_received.anagram_phrase_solution.len() as u32;
            if metrics_received.is_done {
                count_concurrent -= 1;
                add_metrics(&mut metrics, metrics_received);
            }
            if count_success >= (anagram_search_lookups.md5_checksums.len() as u32) {
                println!("Found all solutions in time elapsed: {:?}", start_time.elapsed());
                println!("Phrases Computed: {}, Max Phrase Length: {}", metrics.anagram_phrases_found.to_formatted_string(&Locale::en), metrics.anagram_phrase_max_depth);
                process::exit(0);
            }
        }
    }
    
}


async fn async_traverse_anagram_phrases(
    mut anagram_search: AnagramSearch,
    anagram_search_lookups: AnagramSearchLookups,
    anagram_root: String,
    resume_index: usize,
    tx: Sender<AnagramMetrics>) {

    let mut anagram_metrics: AnagramMetrics = AnagramMetrics{
        anagram_phrases_incomplete: 0,
        anagram_phrase_solution: HashMap::new(),
        anagram_roots_exhausted: 0,
        anagram_phrase_max_depth:0,
        anagram_phrases_found:0,
        is_done:false,};

    let mut anagram_collected_ref: Vec<&String> = Vec::new();
    anagram_collected_ref.push(&anagram_root);

    traverse_anagram_phrases(
            &mut anagram_search,
            &anagram_search_lookups,
            &mut anagram_metrics,
            &mut anagram_collected_ref,
            resume_index,
            &tx);

    // Send a message to the parent task that this task is done.
    anagram_metrics.is_done = true;
    tx.send(anagram_metrics).unwrap();
}

fn traverse_anagram_phrases<'a>(
                anagram_search: &mut AnagramSearch,
                anagram_search_lookups: &'a AnagramSearchLookups,
                anagram_metrics: &mut AnagramMetrics,
                anagrams_collected_ref: &mut Vec<&'a String>,
                resume_index: usize,
                tx: &Sender<AnagramMetrics>) {

    if anagram_search.anagram_chars_search.len() == 0 {
        if anagrams_collected_ref.len() > anagram_metrics.anagram_phrase_max_depth.try_into().unwrap() {
            anagram_metrics.anagram_phrase_max_depth = anagrams_collected_ref.len().try_into().unwrap();
        }

        let mut capacity: usize = 0;
        for anagram_sorted in anagrams_collected_ref.iter() {
            capacity += anagram_sorted.len() + 1;
        }
        let mut anagram_phrase = String::with_capacity(capacity);
        let mut anagram_phrase_vec: Vec<&String> = Vec::new();
        permutate_anagram_sorted(
            anagram_search,
            anagram_search_lookups,
            anagram_metrics,
            anagrams_collected_ref,
            &mut anagram_phrase_vec,
            &mut anagram_phrase, 
            anagrams_collected_ref.len(),
            tx);
        return;
    }

    let anagrams_sorted_vec_ref = &anagram_search_lookups.anagrams_sorted_vec;
    for (anagram_sorted_index, anagram_sorted) in anagrams_sorted_vec_ref.iter().skip(resume_index).enumerate() {
        let anagram_char_count = anagram_search_lookups.anagrams_sorted_chars.get(anagram_sorted).unwrap();
        if !subtract_chars(&mut anagram_search.anagram_chars_search, &anagram_char_count) {
            anagram_metrics.anagram_phrases_incomplete += 1;
            continue;
        }

        anagrams_collected_ref.push(anagram_sorted);

        traverse_anagram_phrases(
            anagram_search,
            anagram_search_lookups,
            anagram_metrics,
            anagrams_collected_ref,
            resume_index + anagram_sorted_index,
            &tx);
            
        anagrams_collected_ref.pop();

        add_chars(&mut anagram_search.anagram_chars_search, &anagram_char_count);
    }
}

fn permutate_anagram_sorted<'a>(
    anagram_search: &mut AnagramSearch, 
    anagram_search_lookups: &'a AnagramSearchLookups,
    anagram_metrics: &mut AnagramMetrics,
    anagrams_collected: &mut Vec<&String>,
    anagram_phrase_vec: &mut Vec<&'a String>,
    anagram_phrase: &mut String,
    size: usize,
    tx: &Sender<AnagramMetrics>) {

    if size == 1 {
        permutate_anagram_words(
            anagram_search,
            anagram_search_lookups,
            anagram_metrics,
            anagrams_collected,
            anagram_phrase_vec,
            anagram_phrase,
            0,
            tx);
        return;
    }

    permutate_anagram_sorted(anagram_search,
        anagram_search_lookups,
        anagram_metrics,
        anagrams_collected,
        anagram_phrase_vec,
        anagram_phrase,
        size - 1,
        tx);

    for idx in 0..size-1 {        
        if size & 1 == 1 {
            anagrams_collected.swap(0, size-1);
        } else {
            anagrams_collected.swap(idx, size - 1);
        }

        permutate_anagram_sorted(anagram_search,
                                   anagram_search_lookups,
                                   anagram_metrics,
                                   anagrams_collected,
                                   anagram_phrase_vec,
                                   anagram_phrase,
                                   size - 1,
                                   tx);
    }

    if size == anagrams_collected.len() {
        if anagrams_collected.len() & 1 == 1 {
            anagrams_collected.swap(0, size - 1);
        } else {
            anagrams_collected.rotate_right(1);
        }
    }
}

fn permutate_anagram_words<'a> (
    anagram_search: &mut AnagramSearch,
    anagram_search_lookups: &'a AnagramSearchLookups,
    anagram_metrics: &mut AnagramMetrics,
    anagrams_collected: &mut Vec<&String>,
    anagram_phrase_vec: &mut Vec<&'a String>,
    anagram_phrase_string: &mut String,
    resume_idx: usize,
    tx: &Sender<AnagramMetrics>) {

    if resume_idx >= anagrams_collected.len() {
        anagram_phrase_string.clear();
        for word in anagram_phrase_vec {
            anagram_phrase_string.push_str(word);
            anagram_phrase_string.push(' ');
        }
        // Get rid of the very last space
        anagram_phrase_string.pop();

        test_md5_checksums(anagram_phrase_string, &anagram_search_lookups.md5_checksums, anagram_metrics, tx);
        return;
    }

    let anagram_sorted: &String = anagrams_collected.index(resume_idx);
    let words = anagram_search_lookups.anagrams_sorted_map.get(anagram_sorted);

    if words.is_none() {
        return;
    }

    for word in words.unwrap().iter() {
        anagram_phrase_vec.push(word);

        permutate_anagram_words(
                anagram_search,
                anagram_search_lookups,
                anagram_metrics,
                anagrams_collected,
                anagram_phrase_vec,
                anagram_phrase_string,
    resume_idx + 1,
                tx);

        anagram_phrase_vec.pop();
    }    
}

// Test if the anagram phrase matches any of the remaining MD5 checksums
fn test_md5_checksums(phrase: &String, md5_checksums: &HashSet<md5::Digest>, anagram_metrics: &mut AnagramMetrics, tx: &Sender<AnagramMetrics>) {
    anagram_metrics.anagram_phrases_found += 1;
    if md5_checksums.contains(&md5::compute(phrase)) {
        //println!("Found phrase: {}, with md5: {:?}", phrase, md5::compute(phrase));
        let anagram_solution_metric: AnagramSolutionMetrics = AnagramSolutionMetrics {
            anagram_phrase_checksum: md5::compute(phrase),
            anagram_phrase_time: std::time::Instant::now(),
        };
        anagram_metrics.anagram_phrase_solution.insert(phrase.clone(), anagram_solution_metric);
        tx.send(anagram_metrics.clone()).unwrap();
    }
}

fn main() {
    // Get the initial data and do some formatting
    let anagram_map = get_anagram_map();
    let (anagram,_search_phrase)= get_anagram();
    let easy = hex::FromHex::from_hex("e4820b45d2277f3844eac66c903e84be").unwrap();
    let medium = hex::FromHex::from_hex("23170acc097c24edb98fc5488ab033fe").unwrap();
    let hard = hex::FromHex::from_hex("665e5bcb0c20062fe8abaaf4628bb154").unwrap();
    let md5_checksums: HashSet<md5::Digest> = HashSet::from([md5::Digest(easy), md5::Digest(medium), md5::Digest(hard)]);
    let anagram_chars : HashMap<char, u32> = count_chars(&anagram);

    // Get the anagram
    let mut anagram_chars_list : HashMap<String, HashMap<char, u32>> = HashMap::new();
    for anagram_sorted in anagram_map.keys() {
        anagram_chars_list.insert(anagram_sorted.clone(), count_chars(anagram_sorted));
    }

    // Filter the anagrams that have more characters than what's provided.
    let mut excluded_count: u32 = 0;
    let mut anagrams_remaining_char_list: HashMap<String, HashMap<char, u32>> = HashMap::new();
    for (anagram_sorted, anagram_counted_chars) in anagram_chars_list.iter() {
        if !contains_chars(&anagram_chars, anagram_counted_chars) {
            excluded_count += 1;
        } else {
            anagrams_remaining_char_list.insert(anagram_sorted.clone(), anagram_counted_chars.clone());
        }
    }

    // Create a vector from the hashmap of anagrams. Vectors are ordered, hashmaps are random.
    // An ordered set is necessary for optimizing the removal of repeated negative searches.
    let mut anagram_map_vec: HashMap<String, Vec<String>> = HashMap::new();
    let mut anagram_sorted_list_vec: Vec<String> = Vec::new();
    for (anagram_sorted, _) in anagrams_remaining_char_list.iter() {
        let anagram_words: &HashSet<String> = anagram_map.get(anagram_sorted).unwrap();
        anagram_map_vec.insert(anagram_sorted.clone(), Vec::from_iter(anagram_words.clone()));
        anagram_sorted_list_vec.push(anagram_sorted.clone());
    }

    // The sort priority is length first then by alphabetical
    // This has a functional impact (optimization)
    // on eliminating as many negatives from
    // the beginning as possible.
    anagram_sorted_list_vec.sort_by(
    |a, b| {
            let mut cmp = a.len().cmp(&b.len());
            if cmp == Ordering::Equal {
                cmp = b.cmp(a);
            }
            cmp
        });
    anagram_sorted_list_vec.reverse();

    // After filtration, print the remaining anagrams to be searched
    println!("Total: {}, Excluded: {}, Remaining: {}", anagram_chars_list.len(), excluded_count, anagram_chars_list.len() as u32 - excluded_count);

    let anagram_search: AnagramSearch = AnagramSearch {
        anagram_chars_search: anagram_chars,
    };

    // Package it all into a neat struct
    let anagram_search_lookups: AnagramSearchLookups = AnagramSearchLookups {
        anagrams_sorted_chars: anagrams_remaining_char_list,
        anagrams_sorted_vec: anagram_sorted_list_vec,
        anagrams_sorted_map: anagram_map_vec,
        md5_checksums,
    };

    // Start searching for the anagram phrases
    search_anagram_phrases(anagram_search, anagram_search_lookups);
}
