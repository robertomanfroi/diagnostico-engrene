import os
import json
import yaml
import sys

# Directory paths
import subprocess
_REPO_ROOT = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
BASE = os.path.join(_REPO_ROOT, "squads", "squad-creator-pro", "minds")
AN_DIR = f"{BASE}/oalanicolas/heuristics"
PV_DIR = f"{BASE}/pedro_valerio/heuristics"

def get_file_path(heuristic_id):
    if heuristic_id.startswith("AN_KE"):
        return os.path.join(AN_DIR, f"{heuristic_id}.md")
    elif heuristic_id.startswith("PV_PA") or heuristic_id.startswith("PV_BS"):
        return os.path.join(PV_DIR, f"{heuristic_id}.md")
    return None

def build_yaml_block(cross_data, source_mind, target_mind):
    """Builds the YAML block for cross_mind_map mapping."""
    lines = ["cross_mind_map:"]
    
    convergent = cross_data.get("convergent", [])
    tension = cross_data.get("tension", [])
    
    if convergent:
        lines.append("  convergent:")
        for item in convergent:
            lines.append(f'    - id: "{item["id"]}"')
            if "title" in item:
                lines.append(f'      title: "{item["title"]}"')
            lines.append(f'      mind: "{target_mind}"')
            lines.append(f'      resonance: "{item["resonance"]}"')
            
    if tension:
        lines.append("  tension:")
        for item in tension:
            lines.append(f'    - id: "{item["id"]}"')
            if "title" in item:
                lines.append(f'      title: "{item["title"]}"')
            lines.append(f'      mind: "{target_mind}"')
            lines.append(f'      divergence: "{item["divergence"]}"')
            lines.append(f'      invalidates: false')
            
    if not convergent and not tension:
        return ""
        
    return "\n".join(lines)

def inject_to_file(filepath, cross_data, target_mind):
    if not os.path.exists(filepath):
        print(f"  [MISSING] {filepath}")
        return False

    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Skip if it already has cross_mind_map
    if 'cross_mind_map:' in content:
        print(f"  [SKIP] {os.path.basename(filepath)} already has cross_mind_map")
        return False

    parts = content.split('---', 2)
    if len(parts) < 3:
        print(f"  [ERROR] {os.path.basename(filepath)} - could not parse frontmatter")
        return False

    cross_yaml = build_yaml_block(cross_data, target_mind, target_mind)
    if not cross_yaml:
        return False

    new_frontmatter = parts[1].rstrip('\n') + '\n' + cross_yaml + '\n'
    new_content = parts[0] + '---' + new_frontmatter + '---' + parts[2]

    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(new_content)
        
    print(f"  [OK] Injected into {os.path.basename(filepath)}")
    return True

def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    json_path = os.path.join(script_dir, 'cross_map.json')
    
    if not os.path.exists(json_path):
        print(f"{json_path} not found!")
        sys.exit(1)
        
    with open(json_path, 'r', encoding='utf-8') as f:
        mappings = json.load(f)

    # mappings is a dict: { "AN_KE_XXX": { "convergent": [...], "tension": [...] } }
    
    # Process Base Mappings (AN files)
    print("=== Processing Main Mapping ===")
    for an_id, data in mappings.items():
        filepath = get_file_path(an_id)
        if filepath:
            inject_to_file(filepath, data, "pedro_valerio")

    # Generate Reciprocal Mappings (PV files)
    print("\n=== Processing Reciprocal Mapping ===")
    pv_mappings = {}
    for an_id, data in mappings.items():
        an_filepath = get_file_path(an_id)
        if not os.path.exists(an_filepath): continue
        
        # We need the title of AN for the PV reciprocal link
        an_title = "Title not retrieved"
        with open(an_filepath, 'r') as f:
            for line in f:
                if line.startswith("title:"):
                    an_title = line.replace("title:", "").replace('"', "").strip()
                    break

        for conv in data.get("convergent", []):
            pv_id = conv["id"]
            if pv_id not in pv_mappings:
                pv_mappings[pv_id] = {"convergent": [], "tension": []}
            pv_mappings[pv_id]["convergent"].append({
                "id": an_id,
                "title": an_title,
                "resonance": conv["resonance"]
            })
            
        for tens in data.get("tension", []):
            pv_id = tens["id"]
            if pv_id not in pv_mappings:
                pv_mappings[pv_id] = {"convergent": [], "tension": []}
            pv_mappings[pv_id]["tension"].append({
                "id": an_id,
                "title": an_title,
                "divergence": tens["divergence"]
            })

    for pv_id, data in pv_mappings.items():
        filepath = get_file_path(pv_id)
        if filepath:
            inject_to_file(filepath, data, "oalanicolas")

if __name__ == "__main__":
    main()
