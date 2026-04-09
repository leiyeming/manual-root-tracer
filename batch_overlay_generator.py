import os
import glob
from create_overlay_from_json import JSONOverlayGenerator

def process_all_folders():
    """Process all JSON files in the specified folders"""
    
    # Define the folder paths
    folders = [
        r"C:\Users\Yeming\OneDrive - The University of Queensland\root length measurements\extracted_images1",
        r"C:\Users\Yeming\OneDrive - The University of Queensland\root length measurements\extracted_images2", 
        r"C:\Users\Yeming\OneDrive - The University of Queensland\root length measurements\extracted_images3",
        r"C:\Users\Yeming\OneDrive - The University of Queensland\root length measurements\extracted_images4"
    ]
    
    # Create the overlay generator
    generator = JSONOverlayGenerator()
    
    total_processed = 0
    total_errors = 0
    
    # Process each folder
    for folder_path in folders:
        print(f"\nProcessing folder: {folder_path}")
        
        if not os.path.exists(folder_path):
            print(f"Warning: Folder does not exist: {folder_path}")
            continue
            
        # Find all JSON files in the folder
        json_pattern = os.path.join(folder_path, "*.json")
        json_files = glob.glob(json_pattern)
        
        if not json_files:
            print(f"No JSON files found in: {folder_path}")
            continue
            
        print(f"Found {len(json_files)} JSON files")
        
        # Process each JSON file
        for json_file in json_files:
            try:
                # Get the base filename without extension
                base_name = os.path.splitext(os.path.basename(json_file))[0]
                
                # Create output path with _ann.png suffix in the same folder
                output_path = os.path.join(folder_path, f"{base_name}_ann.png")
                
                print(f"Processing: {os.path.basename(json_file)} -> {base_name}_ann.png")
                
                # Process the JSON file
                generator.process_json_file(json_file, output_path)
                total_processed += 1
                
            except Exception as e:
                print(f"Error processing {json_file}: {str(e)}")
                total_errors += 1
                continue
    
    print(f"\n=== Processing Complete ===")
    print(f"Total files processed successfully: {total_processed}")
    print(f"Total errors: {total_errors}")

if __name__ == "__main__":
    process_all_folders() 